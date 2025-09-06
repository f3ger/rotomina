import json
import time
import re
import asyncio
import subprocess
import httpx
import zipfile
import shutil
import datetime
import threading
import traceback
import tempfile
import os
import platform
import logging
import hashlib
import xml.etree.ElementTree as ET
from pathlib import Path
from functools import wraps
from typing import List, Dict, Optional, Tuple, Set
from dataclasses import dataclass

from fastapi import FastAPI, Request, Form, BackgroundTasks, WebSocket, WebSocketDisconnect
from fastapi.responses import HTMLResponse, RedirectResponse
from fastapi.staticfiles import StaticFiles
from fastapi.responses import HTMLResponse
from starlette.middleware.sessions import SessionMiddleware
from starlette.templating import Jinja2Templates
from contextlib import asynccontextmanager

# Global Configuration
BASE_DIR = Path(__file__).resolve().parent
CONFIG_FILE = BASE_DIR / "config.json"
APK_DIR = BASE_DIR / "data" / "apks" / "pogo"
EXTRACT_DIR = APK_DIR / "extracted"
POGO_MIRROR_URL = "https://mirror.unownhash.com"
DEFAULT_ARCH = "arm64-v8a"
device_status_cache = {}
update_lock = threading.Lock()
update_in_progress = False
current_progress = 0
devices_in_update = {}  # Format: {device_id: {"in_update": True, "update_type": "pogo/mitm/pif", "started_at": timestamp}}
device_runtimes = {}

# WebSocket Connection Manager
class ConnectionManager:
    def __init__(self):
        self.active_connections: Set[WebSocket] = set()

    async def connect(self, websocket: WebSocket):
        await websocket.accept()
        self.active_connections.add(websocket)
        print(f"WebSocket client connected. Total active connections: {len(self.active_connections)}")

    def disconnect(self, websocket: WebSocket):
        self.active_connections.discard(websocket)
        print(f"WebSocket client disconnected. Remaining connections: {len(self.active_connections)}")

    async def broadcast(self, message: dict):
        disconnected_websockets = set()
        
        for connection in self.active_connections:
            try:
                await connection.send_json(message)
            except Exception as e:
                print(f"Error broadcasting to WebSocket: {e}")
                disconnected_websockets.add(connection)
        
        # Remove disconnected websockets
        for ws in disconnected_websockets:
            self.active_connections.discard(ws)
            
        if disconnected_websockets:
            print(f"Removed {len(disconnected_websockets)} disconnected WebSocket(s). Remaining: {len(self.active_connections)}")

# Initialize WebSocket manager
ws_manager = ConnectionManager()

# ADB Connection Pool - Optimizes connection management
class ADBConnectionPool:
    """
    Manages ADB connections to devices and minimizes
    reconnection attempts by tracking connection status.
    """
    def __init__(self):
        self.connected_devices = set()
        self.last_command_time = {}  # Track when last command was sent to each device
        self.connection_lock = threading.Lock()
    
    def ensure_connected(self, device_id: str) -> bool:
        """
        Ensures device is connected, but only attempts reconnection
        if necessary to avoid unnecessary ADB commands.
        """
        device_id = format_device_id(device_id)
        
        with self.connection_lock:
            # If we've recently confirmed connection, don't check again
            current_time = time.time()
            if (device_id in self.last_command_time and 
                current_time - self.last_command_time[device_id] < 30):  # 30-second threshold
                return True
                
            # Check if already in connected devices list
            if device_id in self.connected_devices:
                # Verify without reconnect attempt
                devices_result = subprocess.run(
                    ["adb", "devices"],
                    capture_output=True,
                    text=True,
                    timeout=TimeoutConfig.SHORT
                )
                
                device_line_pattern = f"{device_id}\tdevice"
                if device_line_pattern in devices_result.stdout:
                    self.last_command_time[device_id] = current_time
                    return True
                
                # If not found, remove from our tracking set
                self.connected_devices.discard(device_id)
            
            # Connect only if needed
            is_network_device = ":" in device_id
            if is_network_device:
                connect_result = subprocess.run(
                    ["adb", "connect", device_id],
                    timeout=TimeoutConfig.MEDIUM,
                    capture_output=True,
                    text=True
                )
                
                if "connected to" in connect_result.stdout and "already" not in connect_result.stdout:
                    print(f"Device {device_id} newly connected")
                
                if "failed" in connect_result.stdout.lower() or "cannot" in connect_result.stdout.lower():
                    return False
            
            # Verify connection
            devices_result = subprocess.run(
                ["adb", "devices"],
                capture_output=True,
                text=True,
                timeout=TimeoutConfig.SHORT
            )
            
            device_line_pattern = f"{device_id}\tdevice"
            if device_line_pattern in devices_result.stdout:
                self.connected_devices.add(device_id)
                self.last_command_time[device_id] = current_time
                return True
            
            return False
    
    def execute_command(self, device_id: str, command: list) -> subprocess.CompletedProcess:
        """
        Executes an ADB command after ensuring connection,
        updates the last command time for the device.
        """
        device_id = format_device_id(device_id)
        if self.ensure_connected(device_id):
            # Handle command format with -s parameter
            if command[0] == "adb" and "-s" not in command:
                command.insert(1, "-s")
                command.insert(2, device_id)
                
            result = subprocess.run(command, capture_output=True, text=True, timeout=TimeoutConfig.LONG)
            
            with self.connection_lock:
                self.last_command_time[device_id] = time.time()
            
            return result
        else:
            # Simulate a failed command result
            return subprocess.CompletedProcess(
                args=command,
                returncode=1,
                stdout="",
                stderr="Device not connected"
            )
    
    def batch_shell_commands(self, device_id: str, commands: list) -> str:
        """
        Executes multiple shell commands in a single ADB call.
        Returns the combined output.
        """
        device_id = format_device_id(device_id)
        if not self.ensure_connected(device_id):
            return ""
            
        # Join commands with separator and error handling
        script = " && echo '---CMD_SEPARATOR---' && ".join(commands)
        
        # Execute as a single shell command
        cmd = ["adb", "-s", device_id, "shell", script]
        result = subprocess.run(cmd, capture_output=True, text=True, timeout=TimeoutConfig.LONG)
        
        with self.connection_lock:
            self.last_command_time[device_id] = time.time()
            
        if result.returncode == 0:
            return result.stdout
        else:
            print(f"Batch command failed: {result.stderr}")
            return ""
            
    def cleanup_connections(self):
        """Cleans up stale connections based on last activity time"""
        current_time = time.time()
        with self.connection_lock:
            stale_devices = []
            for device_id in self.connected_devices:
                if (device_id not in self.last_command_time or
                    current_time - self.last_command_time[device_id] > 300):  # 5 minutes
                    stale_devices.append(device_id)
            
            for device_id in stale_devices:
                self.connected_devices.discard(device_id)
                if device_id in self.last_command_time:
                    del self.last_command_time[device_id]

# Create a global instance
adb_pool = ADBConnectionPool()

# Version Manager - Optimizes version checking
class VersionManager:
    """
    Manages device version information with a long-lived cache
    and only fetches versions when actually needed.
    """
    def __init__(self):
        self.version_cache = {}  # Format: {device_id: {"pogo": "0.251.0", "mitm": "1.5.2", "module": "Fork 3.2", "timestamp": 12345678}}
        self.version_lock = threading.Lock()
        self.forced_refresh_device = set()  # Devices that need forced refresh
        
    def mark_for_refresh(self, device_id):
        """Marks a device for refresh at next query"""
        with self.version_lock:
            self.forced_refresh_device.add(device_id)
            
    def clear_refresh_marker(self, device_id):
        """Removes refresh marker for a device"""
        with self.version_lock:
            self.forced_refresh_device.discard(device_id)
    
    def get_version_info(self, device_id, force_refresh=False):
        """
        Gets version information using individual commands,
        with improved timeout handling and caching.
        
        Args:
            device_id: Device identifier
            force_refresh: Whether to ignore cache
            
        Returns:
            dict: Version information or None on error
        """
        device_id = format_device_id(device_id)
        current_time = time.time()
        
        # Check if cache entry exists and is current
        with self.version_lock:
            needs_refresh = (
                force_refresh or
                device_id in self.forced_refresh_device or
                device_id not in self.version_cache or
                current_time - self.version_cache[device_id].get("timestamp", 0) > 86400  # 24-hour cache lifetime
            )
            
            # If device is in update, use cache regardless
            if device_id in devices_in_update and devices_in_update[device_id]["in_update"]:
                needs_refresh = False
                print(f"Device {device_id} in update process, using cached version info")
            
            # Remove refresh marker if present
            self.forced_refresh_device.discard(device_id)
            
            if not needs_refresh and device_id in self.version_cache:
                return self.version_cache[device_id]
        
        # Initialize version info with defaults
        version_info = {
            "pogo_version": "N/A",
            "mitm_version": "N/A",
            "module_version": "N/A",
            "timestamp": current_time
        }
        
        # Try to get previous values from cache to use as fallback
        previous_info = None
        if device_id in self.version_cache:
            previous_info = self.version_cache[device_id]
        
        success = False
        
        # Use individual commands with shorter timeouts (10 seconds each)
        try:
            # Try PoGo version
            try:
                pogo_cmd = f'adb -s {device_id} shell "dumpsys package com.nianticlabs.pokemongo | grep versionName"'
                pogo_result = subprocess.run(pogo_cmd, shell=True, capture_output=True, text=True, timeout=TimeoutConfig.MEDIUM)
                if pogo_result.returncode == 0 and pogo_result.stdout:
                    pogo_match = re.search(r'versionName=(\d+\.\d+\.\d+)', pogo_result.stdout)
                    if pogo_match:
                        version_info["pogo_version"] = pogo_match.group(1)
                        print(f"Got PoGo version for {device_id}: {version_info['pogo_version']}")
                        success = True
            except Exception as e:
                print(f"Error getting PoGo version for {device_id}: {str(e)}")
            
            # Try MITM version
            try:
                mitm_cmd = f'adb -s {device_id} shell "dumpsys package com.github.furtif.furtifformaps | grep versionName"'
                mitm_result = subprocess.run(mitm_cmd, shell=True, capture_output=True, text=True, timeout=TimeoutConfig.MEDIUM)
                if mitm_result.returncode == 0 and mitm_result.stdout:
                    mitm_match = re.search(r'versionName=(\d+\.\d+(?:\.\d+)?)', mitm_result.stdout)
                    if mitm_match:
                        version_info["mitm_version"] = mitm_match.group(1)
                        print(f"Got MITM version for {device_id}: {version_info['mitm_version']}")
                        success = True
            except Exception as e:
                print(f"Error getting MITM version for {device_id}: {str(e)}")
            
            # Try Fix module
            try:
                fix_cmd = f'adb -s {device_id} shell "su -c \'cat /data/adb/modules/playintegrityfix/module.prop\'"'
                fix_result = subprocess.run(fix_cmd, shell=True, capture_output=True, text=True, timeout=10)
                if fix_result.returncode == 0 and fix_result.stdout:
                    version_match = re.search(r'version=v?(\d+(?:\.\d+)?.*|v?\d+)', fix_result.stdout)
                    if version_match:
                        module_version = version_match.group(1).strip()
                        version_info["module_version"] = f"Fix {module_version}"
                        print(f"Got Fix module version for {device_id}: {version_info['module_version']}")
                        success = True
            except Exception as e:
                print(f"Error getting Fix module version for {device_id}: {str(e)}")
            
            # Try Fork module if Fix not found
            if version_info["module_version"] == "N/A":
                try:
                    fork_cmd = f'adb -s {device_id} shell "su -c \'cat /data/adb/modules/playintegrityfork/module.prop\'"'
                    fork_result = subprocess.run(fork_cmd, shell=True, capture_output=True, text=True, timeout=10)
                    if fork_result.returncode == 0 and fork_result.stdout:
                        version_match = re.search(r'version=v?(\d+(?:\.\d+)?.*|v?\d+)', fork_result.stdout)
                        if version_match:
                            module_version = version_match.group(1).strip()
                            version_info["module_version"] = f"Fork {module_version}"
                            print(f"Got Fork module version for {device_id}: {version_info['module_version']}")
                            success = True
                except Exception as e:
                    print(f"Error getting Fork module version for {device_id}: {str(e)}")
            
            # Update cache if we got at least one value
            if success:
                with self.version_lock:
                    self.version_cache[device_id] = version_info
                print(f"Retrieved version info for {device_id}")
                return version_info
                
        except Exception as e:
            print(f"Error in version checks for {device_id}: {str(e)}")
        
        # Return cached data if we have it, rather than failing completely
        if previous_info:
            print(f"Using cached version info for {device_id} as fallback")
            return previous_info
        
        # If all else fails
        print(f"No version information available for {device_id}")
        return version_info
        
    def get_devices_needing_pogo_update(self, latest_version):
        """
        Finds devices needing a PoGo update
        
        Args:
            latest_version: The latest available PoGo version
            
        Returns:
            list: List of device IDs needing update
        """
        config = load_config()
        devices_to_update = []
        
        for device in config.get("devices", []):
            device_id = device["ip"]
            
            # Check ADB connection only once per device
            connected, error = check_adb_connection(device_id)
            if not connected:
                print(f"Device {device_id} not reachable via ADB, skipping update check: {error}")
                continue
                
            # Get version info from cache (no force refresh)
            version_info = self.get_version_info(device_id, force_refresh=False)
            
            if not version_info:
                print(f"No version information available for {device_id}")
                continue
                
            installed_version = version_info.get("pogo_version", "N/A")
            
            # Compare versions
            if installed_version == "N/A":
                print(f"Device {device_id} has unknown PoGo version, will update")
                devices_to_update.append(device_id)
            elif installed_version != latest_version:
                print(f"Device {device_id} needs update from {installed_version} to {latest_version}")
                devices_to_update.append(device_id)
            else:
                print(f"Device {device_id} already has latest version {latest_version}, skipping")
                
        return devices_to_update
    
def get_devices_needing_module_update(self, latest_version, module_type="fork"):
        """
        Finds devices needing a module update
        
        Args:
            latest_version: The latest available module version
            module_type: The module type ("fork" or "fix")
            
        Returns:
            list: List of device IDs needing update
        """
        config = load_config()
        devices_to_update = []
        
        print(f"Checking {len(config.get('devices', []))} devices in config for module updates")
        
        # Get a set of device IPs from the config for faster lookup
        config_device_ips = {dev["ip"] for dev in config.get("devices", [])}
        
        for device in config.get("devices", []):
            device_id = device["ip"]
            
            # Skip devices that are not in the config (this is a safety check)
            if device_id not in config_device_ips:
                print(f"Device {device_id} not found in config, skipping update check")
                continue
            
            # Check ADB connection only once per device
            connected, error = check_adb_connection(device_id)
            if not connected:
                print(f"Device {device_id} not reachable via ADB, skipping update check: {error}")
                continue
                
            # Get version info from cache (no force refresh)
            version_info = self.get_version_info(device_id, force_refresh=False)
            
            if not version_info:
                print(f"No version information available for {device_id}")
                continue
                
            installed_module = version_info.get("module_version", "N/A").strip()
            
            # Determine module type and version
            if installed_module == "N/A":
                print(f"No Play Integrity module found on {device_id}, will install module")
                devices_to_update.append(device_id)
                continue
                
            module_is_fork = "Fork" in installed_module
            
            # Check if module type needs to be switched
            if (module_type == "fix" and module_is_fork) or (module_type == "fork" and not module_is_fork):
                print(f"Device {device_id} has different module type than preferred, updating to {module_type.upper()}")
                devices_to_update.append(device_id)
                continue
            
            # Extract current version
            if module_is_fork:
                version_match = re.search(r'Fork\s+v?(\d+(?:\.\d+)?.*|v?\d+)', installed_module)
            else:
                version_match = re.search(r'Fix\s+v?(\d+(?:\.\d+)?.*|v?\d+)', installed_module)
                
            if version_match:
                current_version = version_match.group(1)
                print(f"Current module version on {device_id}: {current_version}, available: {latest_version}")
                
                # Compare version numbers
                try:
                    current_tuple = parse_version(current_version)
                    new_tuple = parse_version(latest_version)
                    
                    if current_tuple < new_tuple:
                        print(f"Update needed for {device_id}! Installed: {current_version}, Available: {latest_version}")
                        devices_to_update.append(device_id)
                    else:
                        print(f"Device {device_id} already has latest version, skipping update")
                except (ValueError, AttributeError):
                    print(f"Invalid version format for comparison on {device_id}")
            else:
                print(f"Could not parse version from {installed_module} on {device_id}, scheduling update")
                devices_to_update.append(device_id)
                
        print(f"Found {len(devices_to_update)} devices that need {module_type.upper()} module update")
        
        # Final verification that all devices to update are in the config
        devices_to_update = [dev for dev in devices_to_update if dev in config_device_ips]
        
        return devices_to_update

# Global instance
version_manager = VersionManager()

# Configuration Management
def load_config():
    if not CONFIG_FILE.exists():
        return {"devices": [], "users": []}
    with open(CONFIG_FILE, "r", encoding="utf-8") as f:
        config = json.load(f)
        for device in config.get("devices", []):
            device.setdefault("display_name", device["ip"].split(":")[0])
            device.setdefault("pogo_version", "N/A")
            device.setdefault("mitm_version", "N/A")
            device.setdefault("module_version", "N/A")
            device.setdefault("control_enabled", False)
            device.setdefault("memory_threshold", 200)
        config.setdefault("discord_webhook_url", "")
        config.setdefault("pif_auto_update_enabled", True)
        config.setdefault("pogo_auto_update_enabled", True)
        return config

def save_config(config):
    with open("config.json", "w", encoding="utf-8") as f:
        json.dump(config, f, indent=4)
        f.flush()

def update_device_info(ip: str, details: dict):
    config = load_config()
    for device in config["devices"]:
        if device["ip"] == ip:
            device.update({
                "display_name": details["display_name"],
                "pogo_version": details.get("pogo_version", "N/A"),
                "mitm_version": details.get("mitm_version", "N/A"),
                "module_version": details.get("module_version", "N/A")
            })
    save_config(config)

# Caching Mechanism
def ttl_cache(ttl: int):
    def decorator(func):
        cache = {}
        @wraps(func)
        def wrapper(*args, **kwargs):
            key = (args, tuple(sorted(kwargs.items())))
            now = time.time()
            if key in cache:
                result, timestamp = cache[key]
                if now - timestamp < ttl:
                    return result
            result = func(*args, **kwargs)
            cache[key] = (result, now)
            return result
        def cache_clear():
            cache.clear()
        wrapper.cache_clear = cache_clear
        return wrapper
    return decorator

# Discord Webhook Functions
async def send_discord_notification(message: str, title: str = None, color: int = 0x5865F2):
    """Sends a notification to the Discord webhook, if configured"""
    config = load_config()
    webhook_url = config.get("discord_webhook_url")
    
    if not webhook_url:
        return False
    
    try:
        embed = {
            "title": title or "Rotomina Notification",
            "description": message,
            "color": color,
            "timestamp": datetime.datetime.now(datetime.timezone.utc).isoformat(),
            "footer": {
                "text": "Rotomina"
            }
        }
        
        async with httpx.AsyncClient() as client:
            response = await client.post(
                webhook_url,
                json={
                    "embeds": [embed]
                },
                timeout=10
            )
            
            if response.status_code >= 200 and response.status_code < 300:
                print(f"Discord notification sent: {message}")
                return True
            else:
                print(f"Discord webhook error: {response.status_code} - {response.text}")
                return False
                
    except Exception as e:
        print(f"Error sending Discord notification: {str(e)}")
        return False

# Discord Message Color Constants
DISCORD_COLOR_RED = 0xE74C3C     # Error/Offline
DISCORD_COLOR_GREEN = 0x2ECC71   # Success/Online
DISCORD_COLOR_BLUE = 0x3498DB    # Info/Update
DISCORD_COLOR_ORANGE = 0xE67E22  # Warning/Restart

# Centralized timeout configuration
class TimeoutConfig:
    SHORT = 5      # Quick operations (disconnect, simple checks)  
    MEDIUM = 10    # Standard operations (connect, version checks)
    LONG = 30      # Complex operations (installations, downloads)
    HTTP = 15      # HTTP requests
    ADB_KEYGEN = 10 # ADB key generation

# Helper functions for specific notifications
async def notify_device_offline(device_name: str, ip: str):
    """Notifies when a device goes offline"""
    message = f"⚠️ Device **{device_name}** ({ip}) is offline."
    await send_discord_notification(
        message=message,
        title="Device Offline",
        color=DISCORD_COLOR_RED
    )

async def notify_device_online(device_name: str, ip: str):
    """Notifies when a device comes back online"""
    message = f"✅ Device **{device_name}** ({ip}) is back online and MITM was successfully started."
    await send_discord_notification(
        message=message,
        title="Device Online",
        color=DISCORD_COLOR_GREEN
    )

async def notify_memory_restart(device_name: str, ip: str, memory: int, threshold: int):
    """Notifies when a device is restarted due to low memory"""
    memory_mb = memory / 1024
    memory_formatted = f"{memory_mb:.2f} MB".replace(".", ",")
    
    threshold_formatted = f"{threshold} MB"
    
    message = (f"🔄 Device **{device_name}** ({ip}) is being restarted due to low memory.\n"
              f"Available memory: **{memory_formatted}** (Threshold: {threshold_formatted})")
    
    await send_discord_notification(
        message=message,
        title="Low Memory - Restart",
        color=DISCORD_COLOR_ORANGE
    )

async def notify_update_installed(device_name: str, ip: str, update_type: str, version: str):
    """Notifies when an update has been installed on a device"""
    message = f"📲 **{update_type}** update (Version: {version}) has been installed on device **{device_name}** ({ip})."
    
    await send_discord_notification(
        message=message,
        title=f"{update_type} Update Installed",
        color=DISCORD_COLOR_GREEN
    )

async def notify_update_downloaded(update_type: str, version: str):
    """Notifies when an update has been downloaded"""
    message = f"💾 New **{update_type}** version {version} has been downloaded and is ready for installation."
    
    await send_discord_notification(
        message=message,
        title=f"New {update_type} Version Available",
        color=DISCORD_COLOR_BLUE
    )

# Device update tracking functions
def mark_device_in_update(device_id: str, update_type: str) -> None:
    """Marks a device as being in update process"""
    device_id = format_device_id(device_id)
    devices_in_update[device_id] = {
        "in_update": True,
        "update_type": update_type,
        "started_at": time.time()
    }
    print(f"Device {device_id} marked for {update_type} update - will be excluded from automatic restarts")

def clear_device_update_status(device_id: str) -> None:
    """Removes the update marking from a device"""
    device_id = format_device_id(device_id)
    if device_id in devices_in_update:
        del devices_in_update[device_id]
        print(f"Device {device_id} has completed update - normal monitoring restored")

# ADB Functions - Optimized with connection pool
@ttl_cache(ttl=3600)
def check_adb_connection(device_id: str) -> tuple[bool, str]:
    """
    Checks ADB connection to device with enhanced reliability and retry logic.
    
    Args:
        device_id: Either serial number (USB) or IP:Port (network)
    
    Returns:
        tuple: (is_connected, error_message)
    """
    device_id = format_device_id(device_id)
    is_network_device = ":" in device_id and all(c.isdigit() or c == '.' or c == ':' for c in device_id)
    
    # Retry connection attempts with backoff
    for attempt in range(3):
        try:
            # Initial connection check
            if adb_pool.ensure_connected(device_id):
                return True, ""
            
            # For network devices, try explicit reconnection
            if is_network_device:
                try:
                    # Disconnect first to reset connection state
                    adb_pool.execute_command(device_id, ["adb", "disconnect", device_id], timeout=5)
                    time.sleep(0.5)  # Brief pause for cleanup
                    
                    # Reconnect
                    connect_result = adb_pool.execute_command(
                        device_id, ["adb", "connect", device_id], timeout=10
                    )
                    
                    # Check for specific error patterns
                    stdout = connect_result.stdout.lower()
                    if "failed to authenticate" in stdout:
                        return False, "Authentication error: Device not authorized"
                    elif "already connected" in stdout or "connected to" in stdout:
                        # Verify the connection worked
                        if adb_pool.ensure_connected(device_id):
                            return True, ""
                    elif any(err in stdout for err in ["cannot", "failed", "refused", "unreachable"]):
                        if attempt == 2:  # Last attempt
                            return False, f"Connection failed: {connect_result.stdout.strip()}"
                        continue  # Retry
                        
                except subprocess.TimeoutExpired:
                    if attempt == 2:
                        return False, "Connection timeout"
                    continue
            
            # Final verification
            if adb_pool.ensure_connected(device_id):
                return True, ""
                
            # Wait before retry (exponential backoff)
            if attempt < 2:
                time.sleep(1 * (2 ** attempt))
                
        except Exception as e:
            if attempt == 2:  # Last attempt
                return False, f"Critical ADB error: {str(e)}"
            time.sleep(1)
            continue
    
    return False, "Device connection failed after 3 attempts"

def format_device_id(device_id: str) -> str:
    """
    Formats a device ID for consistent use.
    
    - For IP addresses without a port, adds the default port 5555
    - For serial numbers (without colon), leaves the ID unchanged
    """
    device_id = device_id.strip()
    
    if re.match(r"^\d{1,3}\.\d{1,3}\.\d{1,3}\.\d{1,3}$", device_id):
        return f"{device_id}:5555"
    
    return device_id

# Optimized version of get_device_details that uses VersionManager
def get_device_details(device_id: str) -> dict:
    """
    Optimized version of get_device_details that uses VersionManager
    to minimize ADB calls for version information.
    """
    try:
        config_data = load_config()
        device = next((d for d in config_data["devices"] if d["ip"] == device_id), None)

        if not device:
            if ":" in device_id:
                display_name = device_id.split(":")[0]
            else:
                display_name = f"Device-{device_id[-4:]}" if len(device_id) > 4 else device_id
                
            device = {"ip": device_id, "display_name": display_name}
            config_data["devices"].append(device)
            save_config(config_data)

        details = {
            "display_name": device["display_name"],
            "pogo_version": "N/A",
            "mitm_version": "N/A",
            "module_version": "N/A"
        }

        # Check for device name in config.json - rarely needed operation
        if device["display_name"] == device_id.split(":")[0]:
            try:
                cmd = f'adb -s {device_id} shell "su -c \'cat /data/data/com.github.furtif.furtifformaps/files/config.json\'"'
                result = subprocess.run(cmd, shell=True, capture_output=True, text=True, timeout=5)
                if result.stdout:
                    try:
                        device_config = json.loads(result.stdout)
                        new_name = device_config.get("RotomDeviceName", "").strip()

                        if new_name and new_name != device["display_name"]:
                            print(f"Device {device_id} name changed from '{device['display_name']}' to '{new_name}', updating config.json")
                            device["display_name"] = new_name
                            save_config(config_data)

                        details["display_name"] = device["display_name"]
                    except json.JSONDecodeError:
                        print(f"Device {device_id}: Failed to parse config.json")
            except Exception as e:
                print(f"Error reading device name for {device_id}: {e}")

        # Get version info from VersionManager
        version_info = version_manager.get_version_info(device_id)
        if version_info:
            details["pogo_version"] = version_info.get("pogo_version", "N/A")
            details["mitm_version"] = version_info.get("mitm_version", "N/A")
            details["module_version"] = version_info.get("module_version", "N/A")

        update_device_info(device_id, details)
        return details
    except Exception as e:
        print(f"Device detail error {device_id}: {str(e)}")
        return {
            "display_name": device.get("display_name", device_id.split(":")[0] if ":" in device_id else device_id),
            "pogo_version": "N/A",
            "mitm_version": "N/A",
            "module_version": "N/A"
        }

def ensure_adb_keys() -> str:
    """
    Ensures both ADB private and public keys exist and returns the public key content.
    If keys don't exist or are empty, they are generated.
    Works correctly in Docker/Ubuntu environments.
    
    Returns:
        str: The ADB public key content or empty string if generation fails.
    """
    try:
        if platform.system() == "Windows":
            android_dir = os.path.expanduser("~\\.android")
            adb_private_key = os.path.join(android_dir, "adbkey")
            adb_public_key = os.path.join(android_dir, "adbkey.pub")
        else:
            android_dir = "/root/.android"
            adb_private_key = os.path.join(android_dir, "adbkey")
            adb_public_key = os.path.join(android_dir, "adbkey.pub")
        
        if not os.path.exists(android_dir):
            print(f"Creating Android directory: {android_dir}")
            os.makedirs(android_dir, exist_ok=True)
        
        private_key_exists = os.path.exists(adb_private_key) and os.path.getsize(adb_private_key) > 0
        
        public_key_exists = os.path.exists(adb_public_key) and os.path.getsize(adb_public_key) > 0
        
        if not private_key_exists:
            print(f"Private ADB key not found at {adb_private_key}, generating new keys...")
            try:
                subprocess.run(["adb", "keygen", adb_private_key], check=True, timeout=TimeoutConfig.ADB_KEYGEN)
                private_key_exists = os.path.exists(adb_private_key) and os.path.getsize(adb_private_key) > 0
                print(f"Generated private key with adb keygen: {private_key_exists}")
            except (subprocess.SubprocessError, FileNotFoundError) as e:
                print(f"adb keygen failed: {str(e)}, trying alternative approach...")
                
                try:
                    subprocess.run(
                        ["openssl", "genrsa", "-out", adb_private_key, "2048"],
                        check=True, timeout=10
                    )
                    private_key_exists = os.path.exists(adb_private_key) and os.path.getsize(adb_private_key) > 0
                    print(f"Generated private key with OpenSSL: {private_key_exists}")
                except (subprocess.SubprocessError, FileNotFoundError) as e:
                    print(f"Failed to generate private key with OpenSSL: {str(e)}")
        
        if private_key_exists and not public_key_exists:
            print(f"Public key not found at {adb_public_key}, generating from private key...")
            try:
                subprocess.run(
                    ["openssl", "rsa", "-in", adb_private_key, "-pubout", "-out", adb_public_key],
                    check=True, timeout=10
                )
                public_key_exists = os.path.exists(adb_public_key) and os.path.getsize(adb_public_key) > 0
                print(f"Generated public key: {public_key_exists}")
            except (subprocess.SubprocessError, FileNotFoundError) as e:
                print(f"Failed to generate public key: {str(e)}")
        
        if public_key_exists:
            with open(adb_public_key, "r") as f:
                content = f.read().strip()
                print(f"Found ADB public key ({len(content)} bytes)")
                return content
        else:
            print("Failed to ensure ADB keys exist")
            return ""
    except Exception as e:
        print(f"Error ensuring ADB keys: {str(e)}")
        traceback.print_exc()
        return ""

def sync_system_adb_key():
    """
    Synchronizes the system ADB key from /root/.android/adbkey.pub to BASE_DIR/data/adb/adbkey.pub
    This ensures that the system key is also available in the additional keys directory.
    """
    try:
        if platform.system() == "Windows":
            system_key_path = os.path.expanduser("~\\.android\\adbkey.pub")
        else:
            system_key_path = "/root/.android/adbkey.pub"
        
        additional_keys_dir = BASE_DIR / "data" / "adb"
        target_key_path = additional_keys_dir / "adbkey.pub"
        
        if not os.path.exists(system_key_path):
            print(f"System ADB key not found at {system_key_path}")
            return False
        
        if not additional_keys_dir.exists():
            print(f"Creating additional keys directory: {additional_keys_dir}")
            additional_keys_dir.mkdir(parents=True, exist_ok=True)
        
        with open(system_key_path, "r") as f:
            key_content = f.read().strip()
            
        if not key_content:
            print(f"System ADB key is empty, nothing to sync")
            return False
            
        with open(target_key_path, "w") as f:
            f.write(key_content)
            
        print(f"Successfully synchronized system ADB key to {target_key_path}")
        return True
            
    except Exception as e:
        print(f"Error synchronizing system ADB key: {str(e)}")
        return False

# Optimized ADB Authorization
def streamlined_adb_authorization(device_id: str) -> bool:
    """
    Streamlined approach to ADB authorization using a single script
    rather than multiple separate approaches.
    
    Args:
        device_id: Device identifier
        
    Returns:
        bool: True if keys were installed, False otherwise
    """
    try:
        # Generate a single ADB key and store it to a temporary file
        adb_key = ensure_adb_keys()
        if not adb_key:
            print(f"Failed to generate ADB key for {device_id}")
            return False
            
        with tempfile.NamedTemporaryFile(mode='w+', delete=False) as temp:
            temp_path = temp.name
            temp.write(adb_key)
            temp.flush()
        
        # Push the key file to device
        connected = adb_pool.ensure_connected(device_id)
        if not connected:
            print(f"Cannot connect to device {device_id} for authorization")
            os.unlink(temp_path)
            return False
            
        adb_pool.execute_command(
            device_id,
            ["adb", "push", temp_path, "/sdcard/adbkey.pub"]
        )
        
        # Create a comprehensive installation script that tries all methods at once
        installation_script = """
        set -e
        
        # Check for root
        if ! su -c 'id' | grep -q 'uid=0'; then
            echo "No root access"
            exit 1
        fi
        
        # Enable permissive mode for installation
        su -c 'setenforce 0' || true
        
        # Ensure required directories exist
        su -c 'mkdir -p /data/misc/adb'
        su -c 'mkdir -p /data/data/com.android.adb'
        su -c 'mkdir -p /data/adb'
        
        # Fix any immutable attributes
        su -c 'chattr -i /data/misc/adb/adb_keys 2>/dev/null' || true
        
        # Try multiple install locations at once
        for LOCATION in /data/misc/adb/adb_keys /data/data/com.android.adb/adb_keys /data/adb/adb_keys; do
            DIR=$(dirname "$LOCATION")
            su -c "mkdir -p $DIR"
            su -c "cat /sdcard/adbkey.pub > $LOCATION"
            su -c "chmod 644 $LOCATION"
            su -c "chown system:system $LOCATION" || true
        done
        
        # Enable ADB settings
        su -c 'settings put global adb_enabled 1'
        su -c 'development_settings_enabled 1' || true
        
        # Configure TCP mode
        su -c 'setprop service.adb.tcp.port 5555'
        
        # Restart ADB daemon
        su -c 'stop adbd' || true
        su -c 'start adbd' || true
        
        # Clean up
        rm -f /sdcard/adbkey.pub
        
        # Return to enforcing mode
        su -c 'setenforce 1' || true
        
        echo "INSTALL_SUCCESS"
        """
        
        # Save script to device and execute it
        with tempfile.NamedTemporaryFile(mode='w+', delete=False, suffix='.sh') as script_file:
            script_path = script_file.name
            script_file.write(installation_script)
            script_file.flush()
            script_file.close()
            
            # Push script to device
            adb_pool.execute_command(
                device_id,
                ["adb", "push", script_path, "/data/local/tmp/install_adb_keys.sh"]
            )
            
            # Set executable
            adb_pool.execute_command(
                device_id,
                ["adb", "shell", "chmod 755 /data/local/tmp/install_adb_keys.sh"]
            )
            
            # Execute script
            result = adb_pool.execute_command(
                device_id,
                ["adb", "shell", "su -c 'sh /data/local/tmp/install_adb_keys.sh'"]
            )
            
            # Clean up
            os.unlink(script_path)
            adb_pool.execute_command(
                device_id,
                ["adb", "shell", "rm -f /data/local/tmp/install_adb_keys.sh"]
            )
            
            # Check result
            if "INSTALL_SUCCESS" in result.stdout:
                print(f"ADB keys successfully installed on {device_id}")
                
                # Test connection
                adb_pool.execute_command(device_id, ["adb", "disconnect", device_id])
                time.sleep(2)
                reconnect_result = adb_pool.execute_command(
                    device_id, 
                    ["adb", "connect", device_id]
                )
                
                if "connected to" in reconnect_result.stdout and "unauthorized" not in reconnect_result.stdout:
                    print(f"Successfully reconnected to {device_id} without authorization prompt")
                    return True
                    
                print(f"Connection test passed but reconnection message was: {reconnect_result.stdout}")
                return True
            else:
                print(f"Installation failed. Output: {result.stdout}")
                return False
            
    except Exception as e:
        print(f"Error in streamlined ADB authorization for {device_id}: {str(e)}")
        traceback.print_exc()
        return False

# Optimized App Start and Login Sequence
async def optimized_app_start(device_id: str, run_login: bool = True) -> bool:
    """
    Optimized version of app startup that reduces ADB commands
    by batching operations and using more efficient UI inspection.
    
    Args:
        device_id: Device identifier
        run_login: Whether to perform the login sequence
        
    Returns:
        bool: True if startup successful, False otherwise
    """
    device_id = format_device_id(device_id)
    
    try:
        # Verify this device is in the config
        config = load_config()
        config_device_ips = {dev["ip"] for dev in config.get("devices", [])}
        if device_id not in config_device_ips:
            print(f"Warning: Device {device_id} not found in config, not starting app")
            return False
        
        # Ensure ADB connection
        if not adb_pool.ensure_connected(device_id):
            print(f"Cannot establish ADB connection to {device_id}, app start failed")
            return False
        
        # Force stop both apps in one command
        stop_cmd = "am force-stop com.github.furtif.furtifformaps; am force-stop com.nianticlabs.pokemongo"
        stop_result = adb_pool.execute_command(device_id, ["adb", "shell", stop_cmd])
        
        if stop_result.returncode != 0:
            print(f"Warning: Failed to stop apps on {device_id}: {stop_result.stderr}")
        
        await asyncio.sleep(2)
        
        # Start Furtif app
        start_result = adb_pool.execute_command(
            device_id,
            ["adb", "shell", "am start -n com.github.furtif.furtifformaps/com.github.furtif.furtifformaps.MainActivity"]
        )
        
        if start_result.returncode != 0:
            print(f"Failed to start MITM app on {device_id}: {start_result.stderr}")
            return False
        
        if not run_login:
            return True
            
        # Wait for app to load
        await asyncio.sleep(5)
        
        # Execute login sequence with reduced ADB calls
        login_success = await optimized_login_sequence(device_id)
        
        if login_success:
            print(f"Successfully started and logged into apps on {device_id}")
            return True
        else:
            print(f"App started but login sequence failed on {device_id}")
            return False
            
    except Exception as e:
        print(f"Error in optimized app start for {device_id}: {str(e)}")
        return False

async def optimized_login_sequence(device_id: str, max_retries: int = 3) -> bool:
    """
    Optimized login sequence with improved XML parsing error handling
    Updated for new Discord authorization UI
    
    Args:
        device_id: Device identifier
        max_retries: Maximum number of retry attempts
        
    Returns:
        bool: True if login successful, False otherwise
    """
    device_id = format_device_id(device_id)
    temp_dir = Path(tempfile.mkdtemp())
    
    try:
        # Create a reusable function for UI interaction
        async def find_and_tap_element(search_terms: list, max_attempts: int = 5, 
                                      wait_time: int = 2, partial_match: bool = False,
                                      text_suffix: str = None, just_check: bool = False):
            """Searches UI dump for elements matching search terms and taps them"""
            dump_file = temp_dir / "dump.xml"
            
            for attempt in range(max_attempts):
                # Get UI dump with direct file pull instead of parsing stdout
                try:
                    # First, generate the UI dump - fresh dump for each attempt
                    dump_cmd = 'uiautomator dump /sdcard/dump.xml'
                    dump_result = adb_pool.execute_command(device_id, ["adb", "shell", dump_cmd])
                    
                    if "ERROR" in dump_result.stdout:
                        print(f"UI dump generation error on attempt {attempt+1}: {dump_result.stdout}")
                        await asyncio.sleep(wait_time)
                        continue
                    
                    # Then pull the file instead of trying to parse it directly
                    pull_cmd = ["adb", "pull", "/sdcard/dump.xml", str(dump_file)]
                    pull_result = adb_pool.execute_command(device_id, pull_cmd)
                    
                    if pull_result.returncode != 0 or not dump_file.exists():
                        print(f"Failed to pull UI dump file on attempt {attempt+1}")
                        await asyncio.sleep(wait_time)
                        continue
                    
                    # Parse the file locally with enhanced error handling
                    try:
                        # Check if file is empty or too small
                        if dump_file.stat().st_size < 100:
                            print(f"UI dump file too small ({dump_file.stat().st_size} bytes) on attempt {attempt+1}")
                            await asyncio.sleep(wait_time)
                            continue
                            
                        # Read and validate XML content
                        with open(dump_file, 'r', encoding='utf-8') as f:
                            content = f.read()
                        
                        # Basic validation - must contain expected XML structure
                        if not content.strip().startswith('<?xml') or 'hierarchy' not in content:
                            print(f"Invalid XML structure in UI dump on attempt {attempt+1}")
                            await asyncio.sleep(wait_time)
                            continue
                        
                        tree = ET.parse(dump_file)
                        root = tree.getroot()
                        
                        # Verify we have a valid hierarchy
                        if root.tag != 'hierarchy' or len(root) == 0:
                            print(f"Empty or invalid UI hierarchy on attempt {attempt+1}")
                            await asyncio.sleep(wait_time)
                            continue
                            
                    except (ET.ParseError, UnicodeDecodeError, OSError) as e:
                        print(f"XML parsing error on attempt {attempt+1}: {str(e)}")
                        await asyncio.sleep(wait_time)
                        continue
                    
                    # Debug output - only on first attempt
                    if attempt == 0:
                        clickable_elements = []
                        for elem in root.iter("node"):
                            if elem.get("clickable") == "true" and elem.get("text"):
                                clickable_elements.append(f"{elem.get('text')} (enabled={elem.get('enabled')})")
                        
                        if clickable_elements:
                            print(f"Clickable elements found: {', '.join(clickable_elements)}")
                        else:
                            print("No clickable elements found in UI dump")
                    
                    # Search for matches
                    for elem in root.iter("node"):
                        elem_text = elem.get("text", "")
                        if not elem_text:
                            continue
                            
                        elem_text_lower = elem_text.lower()
                        
                        # Check for direct match
                        found_match = False
                        for term in search_terms:
                            term_lower = term.lower()
                            if term_lower == elem_text_lower or (partial_match and (term_lower in elem_text_lower or elem_text_lower in term_lower)):
                                found_match = True
                                break
                        
                        # Additional check for text suffix if provided
                        if not found_match and text_suffix and text_suffix in elem_text:
                            found_match = True
                            
                        if found_match:
                            # If we're just checking existence, return True
                            if just_check:
                                print(f"Found element: '{elem_text}' (enabled={elem.get('enabled')})")
                                return True
                            
                            # Only tap if clickable and enabled
                            if elem.get("clickable") == "true" and elem.get("enabled") == "true":
                                # Extract coordinates and tap
                                bounds = elem.get("bounds", "")
                                match = re.match(r'\[(\d+),(\d+)\]\[(\d+),(\d+)\]', bounds)
                                if match:
                                    x1, y1, x2, y2 = map(int, match.groups())
                                    center_x, center_y = (x1 + x2) // 2, (y1 + y2) // 2
                                    
                                    # Execute tap
                                    tap_cmd = f'input tap {center_x} {center_y}'
                                    adb_pool.execute_command(device_id, ["adb", "shell", tap_cmd])
                                    print(f"Tapped '{elem_text}' at ({center_x}, {center_y})")
                                    return True
                            else:
                                if elem.get("clickable") == "true" or elem.get("enabled") == "true":
                                    print(f"Found '{elem_text}' but it's not clickable/enabled (clickable={elem.get('clickable')}, enabled={elem.get('enabled')})")
                                if just_check:
                                    return True  # Still return True if just checking existence
                
                except Exception as e:
                    print(f"UI interaction error on attempt {attempt+1}: {str(e)}")
                
                # Wait before next attempt
                await asyncio.sleep(wait_time)
            
            # If we get here, we couldn't find the element after max_attempts
            if not just_check:
                print(f"Failed to find elements matching: {search_terms}")
            return False
            
        # Create a reusable function for swipe gesture
        async def perform_swipe():
            """Performs a swipe gesture from bottom to top (scrolling up)"""
            # Get screen size
            size_cmd = 'wm size'
            result = adb_pool.execute_command(device_id, ["adb", "shell", size_cmd])
            
            # Parse dimensions
            width, height = 1080, 1920  # Default fallback (original function values)
            override_match = re.search(r'Override size:\s*(\d+)x(\d+)', result.stdout)
            if override_match:
                width, height = map(int, override_match.groups())
            else:
                physical_match = re.search(r'Physical size:\s*(\d+)x(\d+)', result.stdout)
                if physical_match:
                    width, height = map(int, physical_match.groups())
            
            # Calculate swipe coordinates (original function coordinates)
            start_x = int(width * 0.5)
            start_y = int(height * 0.70)
            end_x = int(width * 0.5)
            end_y = 1
            
            # Execute swipe
            swipe_cmd = f'input swipe {start_x} {start_y} {end_x} {end_y} 500'
            adb_pool.execute_command(device_id, ["adb", "shell", swipe_cmd])
            print(f"Performed swipe from ({start_x},{start_y}) to ({end_x},{end_y})")
            wait_time=1
            return True
            
        # Function to check if apps are running
        async def check_apps_running():
            """Checks if both apps are running"""
            check_cmd = 'pidof com.nianticlabs.pokemongo; echo "---SEPARATOR---"; pidof com.github.furtif.furtifformaps'
            result = adb_pool.execute_command(device_id, ["adb", "shell", check_cmd])
            
            sections = result.stdout.split("---SEPARATOR---")
            pogo_running = len(sections) > 0 and sections[0].strip() and sections[0].strip().isdigit()
            mitm_running = len(sections) > 1 and sections[1].strip() and sections[1].strip().isdigit()
            
            return pogo_running and mitm_running
        
        # Execute login sequence with improved error handling
        for retry in range(max_retries):
            print(f"Login sequence attempt {retry+1}/{max_retries} for {device_id}")
            
            # Step 1: Click Discord Login
            discord_login_success = await find_and_tap_element(["Discord Login"])
            
            if discord_login_success:
                # Wait longer for Discord page to fully load
                print("Waiting for Discord authorization page to load...")
                await asyncio.sleep(15)  # Increased from 10 to 15 seconds
                
                # Step 2: Check if "Keep Scrolling..." button exists (with more attempts)
                print("Checking for 'Keep Scrolling...' button...")
                scroll_text = ["Keep Scrolling...", "Keep Scrolling"]
                keep_scrolling_exists = await find_and_tap_element(
                    scroll_text, 
                    partial_match=True, 
                    just_check=True, 
                    max_attempts=5,  # Increased from 2 to 5
                    wait_time=3       # Wait 3 seconds between attempts
                )
                
                # Step 3: If Keep Scrolling exists, we need to scroll until Authorize appears
                if keep_scrolling_exists:
                    print("'Keep Scrolling...' button found, need to scroll to reveal Authorize button")
                    
                    # Try scrolling up to 3 times (increased from 2)
                    for scroll_attempt in range(3):
                        await perform_swipe()
                        await asyncio.sleep(3)
                        
                        # Check if Authorize button is now available
                        authorize_text = ["Authorize", "Authorise", "Autorisieren", "Autoriser", "Autorizar", "Autorizzare"]
                        authorize_success = await find_and_tap_element(
                            authorize_text, 
                            max_attempts=3,  # Give it more attempts
                            partial_match=True,
                            wait_time=2
                        )
                        
                        if authorize_success:
                            print(f"Authorize button appeared and clicked after {scroll_attempt + 1} scroll(s)")
                            break
                        else:
                            print(f"Authorize button not yet available after scroll {scroll_attempt + 1}")
                            if scroll_attempt < 2:  # Don't wait after last scroll attempt
                                await asyncio.sleep(2)
                else:
                    # If no Keep Scrolling button, try to find Authorize directly
                    print("No 'Keep Scrolling...' button found, looking for Authorize button directly")
                    authorize_text = ["Authorize", "Authorise", "Autorisieren", "Autoriser", "Autorizar", "Autorizzare"]
                    authorize_success = await find_and_tap_element(
                        authorize_text, 
                        max_attempts=3, 
                        partial_match=True,
                        wait_time=2
                    )
                
                # Continue with the rest of the flow if Authorize was clicked
                if 'authorize_success' in locals() and authorize_success:
                    await asyncio.sleep(3)
                    
                    # Step 4: Recheck Service Status
                    recheck_success = await find_and_tap_element(["Recheck Service Status"], max_attempts=3)
                    
                    if recheck_success:
                        await asyncio.sleep(2)
                        
                        # Step 5: Start service
                        start_success = await find_and_tap_element(["Start service"], max_attempts=3)
                        
                        if start_success:
                            print(f"Clicked all buttons, waiting for apps to initialize...")
                            await asyncio.sleep(30)
                            
                            # Step 6: Verify apps are running
                            if await check_apps_running():
                                print(f"Login sequence completed successfully on {device_id}")
                                return True
            
            # If we get here, retry is needed
            if retry < max_retries - 1:
                print(f"Login sequence failed, retrying {retry+2}/{max_retries}...")
                
                # Restart app for next attempt
                stop_cmd = "am force-stop com.github.furtif.furtifformaps"
                adb_pool.execute_command(device_id, ["adb", "shell", stop_cmd])
                
                await asyncio.sleep(2)
                
                start_cmd = "am start -n com.github.furtif.furtifformaps/com.github.furtif.furtifformaps.MainActivity"
                adb_pool.execute_command(device_id, ["adb", "shell", start_cmd])
                
                await asyncio.sleep(5)
        
        print(f"Login sequence failed after {max_retries} attempts")
        return False
            
    except Exception as e:
        print(f"Error in optimized login sequence for {device_id}: {str(e)}")
        return False
    finally:
        # Clean up
        shutil.rmtree(temp_dir, ignore_errors=True)

# APK Management with UnownHash Mirror
@ttl_cache(ttl=3600)
def get_available_versions() -> Dict:
    try:
        response = httpx.get(
            f"{POGO_MIRROR_URL}/index.json",
            timeout=10
        )
        if response.status_code != 200:
            print("Error: Mirror returned status code", response.status_code)
            return {"latest": {}, "previous": {}}

        versions_data = response.json()
        
        processed = []
        for entry in versions_data:
            if entry["arch"] != DEFAULT_ARCH:
                continue
                
            clean_version = entry["version"].replace(".apkm", "")
            processed.append({
                "version": clean_version,
                "filename": f"com.nianticlabs.pokemongo_{DEFAULT_ARCH}_{clean_version}.apkm",
                "url": f"{POGO_MIRROR_URL}/apks/com.nianticlabs.pokemongo_{DEFAULT_ARCH}_{clean_version}.apkm",
                "date": entry.get("date", ""),
                "arch": DEFAULT_ARCH
            })

        sorted_versions = sorted(
            processed,
            key=lambda x: [int(n) for n in x["version"].split(".")],
            reverse=True
        )
        
        distinct_versions = []
        seen_versions = set()
        
        for version in sorted_versions:
            ver = version["version"]
            if ver not in seen_versions:
                distinct_versions.append(version)
                seen_versions.add(ver)
        
        if distinct_versions:
            latest_ver = distinct_versions[0]["version"] if distinct_versions else "N/A"
            prev_ver = distinct_versions[1]["version"] if len(distinct_versions) > 1 else "N/A"
            print(f"Found versions - Latest: {latest_ver}, Previous: {prev_ver}")
        else:
            print("No versions found")
        
        return {
            "latest": distinct_versions[0] if distinct_versions else {},
            "previous": distinct_versions[1] if len(distinct_versions) > 1 else {}
        }
        
    except Exception as e:
        print(f"Mirror check error: {str(e)}")
        return {"latest": {}, "previous": {}}

def download_apk(version_info: Dict) -> Path:
    try:
        print(f"Downloading {version_info['filename']}...")
        response = httpx.get(version_info["url"], follow_redirects=True)
        target_path = APK_DIR / version_info["filename"]
        
        with open(target_path, "wb") as f:
            f.write(response.content)
        
        get_available_versions.cache_clear()
        print(f"Successfully downloaded {version_info['version']} and cleared version cache")
        
        return target_path
    except Exception as e:
        print(f"Download failed: {str(e)}")
        raise

def ensure_latest_apk_downloaded():
    APK_DIR.mkdir(parents=True, exist_ok=True)
    versions = get_available_versions()
    
    if not versions.get("latest"):
        print("No latest version information available")
        return
        
    latest_version = versions["latest"]["version"]
    print(f"Latest available version: {latest_version}")
    
    target_file = APK_DIR / versions["latest"]["filename"]
    if not target_file.exists():
        print(f"New version {latest_version} not found locally, downloading")
        download_apk(versions["latest"])
        asyncio.create_task(notify_update_downloaded("Pokemon GO", latest_version))
        asyncio.create_task(update_ui_with_new_version())
    else:
        print(f"Latest version {latest_version} already downloaded")

async def update_ui_with_new_version():
    """Updates all connected WebSocket clients with new version information"""
    try:
        await asyncio.sleep(1)
        
        get_available_versions.cache_clear()
        
        status_data = await get_status_data()
        
        latest = status_data.get("pogo_latest", "N/A")
        previous = status_data.get("pogo_previous", "N/A")
        print(f"Sending WebSocket update with versions - Latest: {latest}, Previous: {previous}")
        
        await ws_manager.broadcast(status_data)
        print("WebSocket update for new PoGo version sent successfully")
    except Exception as e:
        print(f"Error sending WebSocket update: {str(e)}")
        import traceback
        traceback.print_exc()

def unzip_apk(apk_path: Path, extract_dir: Path):
    try:
        extract_dir.mkdir(parents=True, exist_ok=True)
        
        if any(extract_dir.iterdir()):
            print(f"APK already extracted to {extract_dir}, skipping extraction")
            return
            
        print(f"Extracting {apk_path} to {extract_dir}")
        with zipfile.ZipFile(apk_path, 'r') as zip_ref:
            zip_ref.extractall(extract_dir)
    except zipfile.BadZipFile:
        print(f"Invalid ZIP file: {apk_path}")
        shutil.rmtree(extract_dir)
        raise
    except Exception as e:
        print(f"Error during extraction: {str(e)}")
        raise

# Optimized APK Installation
async def optimized_apk_installation(device_id: str, apk_files: list) -> tuple[bool, str]:
    """
    Optimized APK installation with improved error detection.
    
    Args:
        device_id: Device identifier
        apk_files: List of APK files to install
        
    Returns:
        tuple: (success, error_message)
    """
    device_id = format_device_id(device_id)
    
    try:
        print(f"Starting optimized APK installation for {device_id}")
        
        if not adb_pool.ensure_connected(device_id):
            return False, "Cannot connect to device"
            
        # Single APK case - direct install
        if len(apk_files) == 1:
            print(f"Installing single APK: {apk_files[0]}")
            result = adb_pool.execute_command(
                device_id,
                ["adb", "install", "-r", str(apk_files[0])]
            )
            
            if result.returncode != 0:
                error_msg = result.stderr
                
                # Detect specific error types
                if "INSTALL_FAILED_INSUFFICIENT_STORAGE" in error_msg:
                    print(f"Insufficient storage on {device_id} for APK installation")
                    return False, "INSUFFICIENT_STORAGE"
                elif "INSTALL_FAILED_ALREADY_EXISTS" in error_msg:
                    return False, "ALREADY_EXISTS"
                elif "INSTALL_FAILED_VERSION_DOWNGRADE" in error_msg:
                    return False, "VERSION_DOWNGRADE"
                else:
                    print(f"APK installation failed: {error_msg}")
                    return False, f"INSTALLATION_ERROR: {error_msg}"
                    
            print(f"APK installed successfully on {device_id}")
            return True, "SUCCESS"
            
        # Multiple APK case
        print(f"Installing multiple APKs: {len(apk_files)} files")
        cmd = ["adb", "-s", device_id, "install-multiple", "-r"]
        cmd.extend([str(f) for f in apk_files])
        
        result = subprocess.run(cmd, capture_output=True, text=True, timeout=300)
        
        if result.returncode != 0:
            error_msg = result.stderr
            
            # Also detect specific error types for multiple APKs
            if "INSTALL_FAILED_INSUFFICIENT_STORAGE" in error_msg:
                print(f"Insufficient storage on {device_id} for APK installation")
                return False, "INSUFFICIENT_STORAGE"
            else:
                print(f"Multiple APK installation failed: {error_msg}")
                return False, f"INSTALLATION_ERROR: {error_msg}"
                
        print(f"Multiple APKs installed successfully on {device_id}")
        return True, "SUCCESS"
            
    except Exception as e:
        print(f"APK installation error for {device_id}: {str(e)}")
        return False, f"EXCEPTION: {str(e)}"

async def clear_app_cache(device_id: str) -> bool:
    """
    Clears Pokemon GO app cache to free up storage space.
    
    Args:
        device_id: Device identifier
        
    Returns:
        bool: True if cache clearing was successful
    """
    device_id = format_device_id(device_id)
    
    try:
        print(f"Clearing Pokemon GO cache on {device_id}")
        
        if not adb_pool.ensure_connected(device_id):
            print(f"Cannot connect to {device_id} for cache clearing")
            return False
        
        # Clear app data and cache
        clear_cmd = "pm clear com.nianticlabs.pokemongo"
        result = adb_pool.execute_command(
            device_id,
            ["adb", "shell", clear_cmd]
        )
        
        if "Success" in result.stdout:
            print(f"Successfully cleared Pokemon GO cache on {device_id}")
            return True
        else:
            print(f"Failed to clear Pokemon GO cache on {device_id}: {result.stderr}")
            return False
            
    except Exception as e:
        print(f"Error clearing cache on {device_id}: {str(e)}")
        return False
    
async def uninstall_pogo(device_id: str) -> bool:
    """
    Uninstalls Pokemon GO to free up storage for new installation.
    
    Args:
        device_id: Device identifier
        
    Returns:
        bool: True if uninstallation was successful
    """
    device_id = format_device_id(device_id)
    
    try:
        print(f"Uninstalling Pokemon GO on {device_id}")
        
        if not adb_pool.ensure_connected(device_id):
            print(f"Cannot connect to {device_id} for uninstallation")
            return False
        
        # Uninstall the app
        uninstall_cmd = "pm uninstall com.nianticlabs.pokemongo"
        result = adb_pool.execute_command(
            device_id,
            ["adb", "shell", uninstall_cmd]
        )
        
        if "Success" in result.stdout:
            print(f"Successfully uninstalled Pokemon GO on {device_id}")
            return True
        else:
            print(f"Failed to uninstall Pokemon GO on {device_id}: {result.stderr}")
            return False
            
    except Exception as e:
        print(f"Error uninstalling app on {device_id}: {str(e)}")
        return False

async def optimized_perform_installation(device_ip: str, extract_dir: Path) -> bool:
    """
    Optimized version of the full installation process with
    staged approach for handling storage issues.
    
    Args:
        device_ip: Device identifier
        extract_dir: Directory containing extracted APK files
        
    Returns:
        bool: True if the complete process was successful
    """
    try:
        # Mark device as in update
        mark_device_in_update(device_ip, "pogo")
        update_progress(10)
        
        device_details = get_device_details(device_ip)
        device_name = device_details.get("display_name", device_ip.split(":")[0])
        
        # Find APK files
        apk_files = list(extract_dir.glob("*.apk"))
        if not apk_files:
            print(f"No APK files found in {extract_dir}")
            clear_device_update_status(device_ip)
            return False
            
        update_progress(20)
        
        # Extract version from directory
        version = extract_dir.name
        
        # Try installation with progressive recovery strategies
        strategies = [
            ("normal", None, 60),
            ("cache_clear", clear_app_cache, 50),  
            ("uninstall_reinstall", uninstall_pogo, 55)
        ]
        
        for strategy_name, recovery_action, progress_target in strategies:
            print(f"Attempting {strategy_name} installation on {device_ip}")
            
            # Execute recovery action if needed
            if recovery_action:
                if strategy_name == "cache_clear":
                    await send_discord_notification(
                        message=f"⚠️ Insufficient storage on **{device_name}** ({device_ip}). Clearing cache and retrying.",
                        title="Installation Retry - Clearing Cache",
                        color=DISCORD_COLOR_ORANGE
                    )
                    update_progress(30)
                    recovery_success = await recovery_action(device_ip)
                    update_progress(40)
                elif strategy_name == "uninstall_reinstall":
                    await send_discord_notification(
                        message=f"⚠️ Cache clearing insufficient on **{device_name}** ({device_ip}). Uninstalling and reinstalling Pokemon GO.",
                        title="Installation Retry - Uninstalling", 
                        color=DISCORD_COLOR_ORANGE
                    )
                    update_progress(40)
                    recovery_success = await recovery_action(device_ip)
                    update_progress(45)
                
                if not recovery_success:
                    print(f"Recovery action {strategy_name} failed on {device_ip}")
                    continue
            
            # Try installation
            installation_success, error_msg = await optimized_apk_installation(device_ip, apk_files)
            update_progress(progress_target)
            
            if installation_success:
                print(f"{strategy_name.title()} installation successful on {device_ip}")
                break
            elif error_msg != "INSUFFICIENT_STORAGE":
                # Non-storage error, don't continue with other strategies
                print(f"Installation failed with non-storage error on {device_ip}: {error_msg}")
                break
        
        # Handle final failure
        if not installation_success:
            await send_discord_notification(
                message=f"❌ All installation attempts failed on **{device_name}** ({device_ip}). Final error: {error_msg}",
                title="Installation Failed",
                color=DISCORD_COLOR_RED
            )
            clear_device_update_status(device_ip)
            return False
        
        # Proceed with starting the app if any stage succeeded
        if installation_success:
            # Determine if app control is enabled
            config = load_config()
            device = next((d for d in config["devices"] if d["ip"] == device_ip), None)
            control_enabled = device and device.get("control_enabled", False)
            
            update_progress(70)
            
            # Start app
            print(f"Starting app on {device_ip} after update... (Control enabled: {control_enabled})")
            start_result = await optimized_app_start(device_ip, control_enabled)
            
            if start_result:
                print(f"Successfully started app on {device_ip} after update")
                # Send success notification
                await notify_update_installed(device_name, device_ip, "Pokemon GO", version)
            else:
                print(f"Failed to start app on {device_ip} after update")
                await send_discord_notification(
                    message=f"⚠️ Pokemon GO v{version} was installed on **{device_name}** ({device_ip}) but the app could not be started.",
                    title="Installation OK, Startup Failed",
                    color=DISCORD_COLOR_ORANGE
                )
                
            update_progress(90)
            
            # Clear caches
            device_status_cache.clear()
            version_manager.mark_for_refresh(device_ip)
            
            update_progress(100)
            
            # Update UI
            status_data = await get_status_data()
            await ws_manager.broadcast(status_data)
            
            await asyncio.sleep(2)
            return start_result
        
        # This point should not be reached if everything worked correctly
        clear_device_update_status(device_ip)
        return False
            
    except Exception as e:
        print(f"Installation process error for {device_ip}: {str(e)}")
        # Notify of general errors
        try:
            device_details = get_device_details(device_ip)
            device_name = device_details.get("display_name", device_ip.split(":")[0])
            await send_discord_notification(
                message=f"❌ Pokemon GO update on **{device_name}** ({device_ip}) failed with exception: {str(e)}",
                title="Update Failed - Exception",
                color=DISCORD_COLOR_RED
            )
        except:
            pass
        return False
    finally:
        # Always clear update status
        clear_device_update_status(device_ip)

# Optimized PoGO Auto-Update Task
async def optimized_pogo_update_task():
    """Automatic PoGO update check and installation on devices with reduced version queries"""
    import random
    
    while True:
        try:
            config = load_config()
            
            print("🔍 Checking for PoGO updates...")
            
            # Get versions and download latest version
            get_available_versions.cache_clear()
            versions = get_available_versions()
            
            if not versions.get("latest"):
                print("❌ No valid PoGO version available, skipping check.")
                await asyncio.sleep(3 * 3600)
                continue
                
            latest_version = versions["latest"]["version"]
            print(f"📌 Latest available PoGO version: {latest_version}")
            
            # Always download latest version
            ensure_latest_apk_downloaded()
            
            # Check if auto updates are enabled
            if not config.get("pogo_auto_update_enabled", True):
                print("PoGO auto-update is disabled in configuration. Updates downloaded but not installed.")
                await asyncio.sleep(3 * 3600)
                continue
            
            # Prepare APK
            apk_file = APK_DIR / versions["latest"]["filename"]
            version_extract_dir = EXTRACT_DIR / latest_version
            unzip_apk(apk_file, version_extract_dir)
            
            # Get config device IPs for filtering
            config_device_ips = {dev["ip"] for dev in config.get("devices", [])}
            
            # Find devices needing update - OPTIMIZED: Uses VersionManager
            devices_to_update = version_manager.get_devices_needing_pogo_update(latest_version)
            
            # Filter devices not in config
            devices_to_update = [dev for dev in devices_to_update if dev in config_device_ips]
            
            update_count = len(devices_to_update)
            if update_count > 0:
                print(f"🚀 Installing PoGO version {latest_version} on {update_count} devices that need updates")
                
                # Process each device
                for device_id in devices_to_update:
                    await optimized_perform_installation(device_id, version_extract_dir)
                    # Mark device for version refresh
                    version_manager.mark_for_refresh(device_id)
                
                print("✅ PoGO automatic update complete")
                
                status_data = await get_status_data()
                await ws_manager.broadcast(status_data)
            else:
                print("✅ All devices already have the latest version. No updates needed.")
            
        except Exception as e:
            print(f"❌ PoGO Auto-Update Error: {str(e)}")
            import traceback
            traceback.print_exc()
            
        await asyncio.sleep(3 * 3600)

@dataclass
class MapWorldConfig:
    download_url: str = "https://protomines.ddns.net/apk/MapWorld-release.zip"
    apk_dir: Path = BASE_DIR / "data" / "apks"
    apk_base_name: str = "mapworld"
    package_name: str = "com.github.furtif.furtifformaps"  # Adjust to actual MapWorld package
    cache_file: Path = BASE_DIR / "data" / "mapworld_metadata_cache"
    check_interval_hours: int = 1
    download_timeout: int = 300
    metadata_timeout: int = 10
    max_retries: int = 3
    cache_ttl_minutes: int = 30
    keep_previous_versions: int = 1  # Number of previous versions to keep

# Logger setup
logger = logging.getLogger(__name__)

class MapWorldUpdater:
    """Optimized class for MapWorld updates with version management and better error handling"""
    
    def __init__(self, config: MapWorldConfig = None):
        self.config = config or MapWorldConfig()
        self._metadata_cache = {}
        self._cache_timestamp = 0
        
        # Ensure APK directory exists
        self.config.apk_dir.mkdir(parents=True, exist_ok=True)
    
    def extract_apk_version(self, apk_path: Path, debug: bool = False) -> Tuple[str, str]:
        """Extracts version name and code from APK using Android Binary XML UTF-16 parsing"""
    
        try:
            with zipfile.ZipFile(apk_path, 'r') as zip_file:
                manifest_data = zip_file.read('AndroidManifest.xml')
            
                if debug:
                    logger.info(f"DEBUG: AndroidManifest.xml size: {len(manifest_data)} bytes")
            
                # Check for Android Binary XML magic bytes
                if len(manifest_data) < 4 or manifest_data[:4] != b'\x03\x00\x08\x00':
                    raise Exception("Not a valid Android Binary XML file")
            
                if debug:
                    logger.info("DEBUG: Detected Android Binary XML format")
            
                # UTF-16LE decoding (proven method from debugger)
                try:
                    decoded = manifest_data.decode('utf-16le', errors='ignore')
                    version_matches = re.findall(r'(\d+\.\d+(?:\.\d+)?)', decoded)
                
                    if debug:
                        logger.info(f"DEBUG: UTF-16LE found versions: {version_matches}")
                
                    # Filter for valid versions and select the best one
                    valid_versions = [v for v in version_matches if self._is_valid_version(v)]
                
                    if valid_versions:
                        # Remove duplicates and sort by version number (highest first)
                        unique_versions = list(set(valid_versions))
                        unique_versions.sort(key=lambda x: [int(p) for p in x.split('.')], reverse=True)
                    
                        best_version = unique_versions[0]
                        if debug:
                            logger.info(f"DEBUG: Selected version {best_version} from UTF-16LE decoding")
                    
                        return best_version, "0"
                
                except Exception as e:
                    if debug:
                        logger.debug(f"DEBUG: UTF-16LE decoding failed: {e}")
                    raise Exception("UTF-16LE decoding failed")
        
            # If we get here, the method failed
            raise Exception("No valid version found in AndroidManifest.xml")
        
        except Exception as e:
            logger.error(f"Version extraction failed for {apk_path}: {e}")
            return "unknown", "0"

    def _is_valid_version(self, version: str) -> bool:
        """Checks if a version number makes sense - extended validation"""
        try:
            # Basic validation
            if not version or len(version.split('.')) > 4:
                return False
            
            # Check if it has numeric parts
            parts = version.split('.')
            for part in parts:
                if not part.isdigit():
                    return False
                if int(part) > 999:  # Unrealistic version number
                    return False
            
            # Special validation for modern apps
            if len(parts) >= 2:
                major, minor = int(parts[0]), int(parts[1])
                
                # Modern MapWorld versions should be >= 2.0
                # 1.x versions are probably wrong
                if major == 1 and minor <= 20:
                    logger.debug(f"Rejecting suspicious version {version} (likely too old)")
                    return False
                
                # Realistic version ranges
                if 0 <= major <= 10 and 0 <= minor <= 99:
                    return True
            
            return False
        except:
            return False
    
    def get_versioned_filename(self, version_name: str, version_code: str) -> str:
        """Generates versioned filename"""
        # Clean version name for filename
        clean_version = "".join(c for c in version_name if c.isalnum() or c in ".-_")
        return f"{self.config.apk_base_name}_v{clean_version}_{version_code}.apk"
    
    def get_current_apk_path(self) -> Optional[Path]:
        """Finds the most current APK file"""
        apk_files = list(self.config.apk_dir.glob(f"{self.config.apk_base_name}_v*.apk"))
        if not apk_files:
            return None
        
        # Sort by modification date (newest first)
        apk_files.sort(key=lambda x: x.stat().st_mtime, reverse=True)
        return apk_files[0]
    
    def get_all_apk_versions(self) -> list[Tuple[Path, str, str]]:
        """Returns all available APK versions, sorted by date"""
        apk_files = list(self.config.apk_dir.glob(f"{self.config.apk_base_name}_v*.apk"))
        versions = []
        
        for apk_path in apk_files:
            try:
                version_name, version_code = self.extract_apk_version(apk_path)
                versions.append((apk_path, version_name, version_code))
            except Exception as e:
                logger.warning(f"Could not read version from {apk_path}: {e}")
        
        # Sort by modification date (newest first)
        versions.sort(key=lambda x: x[0].stat().st_mtime, reverse=True)
        return versions
    
    def cleanup_old_versions(self):
        """Removes old APK versions, keeps only the newest ones"""
        versions = self.get_all_apk_versions()
        
        if len(versions) <= self.config.keep_previous_versions + 1:
            return  # Nothing to clean up
        
        # Keep the newest (keep_previous_versions + 1) versions
        to_keep = versions[:self.config.keep_previous_versions + 1]
        to_remove = versions[self.config.keep_previous_versions + 1:]
        
        for apk_path, version_name, version_code in to_remove:
            try:
                apk_path.unlink()
                logger.info(f"Removed old version: {apk_path.name} (v{version_name})")
            except Exception as e:
                logger.error(f"Error removing old APK {apk_path}: {e}")
    
    def backup_current_version(self) -> Optional[Path]:
        """Creates backup of current version before downloading new one"""
        current_apk = self.get_current_apk_path()
        if not current_apk or not current_apk.exists():
            return None
        
        try:
            # Create backup with _backup suffix
            backup_name = current_apk.stem + "_backup" + current_apk.suffix
            backup_path = current_apk.parent / backup_name
            
            shutil.copy2(current_apk, backup_path)
            logger.info(f"Created backup: {backup_path.name}")
            return backup_path
        except Exception as e:
            logger.error(f"Error creating backup: {e}")
            return None

    async def get_remote_metadata(self) -> Dict:
        """Cached metadata retrieval with exponential backoff"""
        now = datetime.datetime.now().timestamp()
        cache_valid_until = self._cache_timestamp + (self.config.cache_ttl_minutes * 60)
        
        # Return cached data if still valid
        if self._metadata_cache and now < cache_valid_until:
            logger.debug("Using cached metadata")
            return self._metadata_cache
        
        for attempt in range(self.config.max_retries):
            try:
                async with httpx.AsyncClient() as client:
                    response = await client.head(
                        self.config.download_url, 
                        timeout=self.config.metadata_timeout
                    )
                    
                    if response.status_code == 200:
                        metadata = {
                            "last_modified": response.headers.get("last-modified", ""),
                            "content_length": response.headers.get("content-length", ""),
                            "etag": response.headers.get("etag", "")
                        }
                        
                        # Cache successful result
                        self._metadata_cache = metadata
                        self._cache_timestamp = now
                        logger.info("Successfully retrieved and cached metadata")
                        return metadata
                    else:
                        logger.warning(f"HTTP {response.status_code} when fetching metadata")
                        
            except httpx.TimeoutException:
                logger.warning(f"Timeout on attempt {attempt + 1}/{self.config.max_retries}")
            except httpx.RequestError as e:
                logger.error(f"Request error on attempt {attempt + 1}: {e}")
            except Exception as e:
                logger.error(f"Unexpected error on attempt {attempt + 1}: {e}")
            
            if attempt < self.config.max_retries - 1:
                wait_time = 2 ** attempt  # Exponential backoff
                logger.info(f"Retrying in {wait_time} seconds...")
                await asyncio.sleep(wait_time)
        
        logger.error("Failed to retrieve metadata after all retries")
        return {}

    def _parse_last_modified(self, last_modified_str: str) -> Optional[float]:
        """Robust parsing of Last-Modified header"""
        if not last_modified_str:
            return None
            
        # Support various date formats
        formats = [
            "%a, %d %b %Y %H:%M:%S %Z",
            "%a, %d %b %Y %H:%M:%S GMT",
            "%a, %d-%b-%Y %H:%M:%S %Z"
        ]
        
        for fmt in formats:
            try:
                return datetime.datetime.strptime(last_modified_str, fmt).timestamp()
            except ValueError:
                continue
        
        logger.warning(f"Could not parse last-modified header: {last_modified_str}")
        return None

    async def has_update_available(self) -> Tuple[bool, str]:
        """Improved update check with detailed feedback"""
        current_apk = self.get_current_apk_path()
        
        if not current_apk or not current_apk.exists():
            return True, "No local APK file exists"

        try:
            remote_meta = await self.get_remote_metadata()
            if not remote_meta:
                return False, "Could not retrieve remote metadata"

            # ETag-based comparison (most reliable)
            if remote_meta.get("etag"):
                local_etag = await self._get_local_file_etag(current_apk)
                remote_etag = remote_meta["etag"].strip('"')
                if local_etag != remote_etag:
                    return True, f"ETag mismatch: local={local_etag}, remote={remote_etag}"

            # Fallback to timestamp and size comparison
            remote_modified_str = remote_meta.get("last_modified")
            if remote_modified_str:
                remote_modified = self._parse_last_modified(remote_modified_str)
                if remote_modified:
                    local_modified = current_apk.stat().st_mtime
                    if remote_modified > local_modified:
                        return True, f"Remote file is newer: {datetime.datetime.fromtimestamp(remote_modified)}"

            # Size comparison
            content_length = remote_meta.get("content_length")
            if content_length and content_length.isdigit():
                remote_size = int(content_length)
                local_size = current_apk.stat().st_size
                if remote_size != local_size:
                    return True, f"Size mismatch: local={local_size}, remote={remote_size}"

            return False, "No updates available"

        except Exception as e:
            logger.error(f"Error checking for updates: {e}")
            return False, f"Error during update check: {str(e)}"

    async def _get_local_file_etag(self, file_path: Path) -> str:
        """Generates ETag-like hash for local file"""
        try:
            hasher = hashlib.md5()
            with open(file_path, 'rb') as f:
                for chunk in iter(lambda: f.read(4096), b""):
                    hasher.update(chunk)
            return hasher.hexdigest()
        except Exception as e:
            logger.error(f"Error generating local file hash: {e}")
            return ""

    async def download_mapworld(self, progress_callback=None, force_version: str = None) -> Tuple[bool, Optional[Path]]:
        """Async download with improved version detection"""
        try:
            # Backup current version if exists
            backup_path = self.backup_current_version()
            
            # Ensure parent directory exists
            self.config.apk_dir.mkdir(parents=True, exist_ok=True)
            
            # Download to temporary file first
            temp_path = self.config.apk_dir / f"{self.config.apk_base_name}_temp_download.apk"
            
            # Try to extract version from URL or response headers first
            download_version = force_version
            
            async with httpx.AsyncClient() as client:
                # First, get headers to check for version hints
                if not download_version:
                    try:
                        head_response = await client.head(self.config.download_url)
                        content_disposition = head_response.headers.get('content-disposition', '')
                        if 'filename=' in content_disposition:
                            suggested_filename = content_disposition.split('filename=')[1].strip('"\'')
                            logger.debug(f"Server suggested filename: {suggested_filename}")
                            
                            # Try to extract version from suggested filename
                            version_match = re.search(r'(\d+\.\d+(?:\.\d+)?)', suggested_filename)
                            if version_match and self._is_valid_version(version_match.group(1)):
                                download_version = version_match.group(1)
                                logger.info(f"Found version in server filename: {download_version}")
                    except Exception as e:
                        logger.debug(f"Could not get version from headers: {e}")
                
                # Download the file
                async with client.stream(
                    "GET", 
                    self.config.download_url, 
                    timeout=self.config.download_timeout
                ) as response:
                    response.raise_for_status()
                    
                    total_size = int(response.headers.get("content-length", 0))
                    downloaded = 0
                    
                    with open(temp_path, "wb") as f:
                        async for chunk in response.aiter_bytes(chunk_size=8192):
                            f.write(chunk)
                            downloaded += len(chunk)
                            
                            if progress_callback and total_size > 0:
                                progress = (downloaded / total_size) * 100
                                await progress_callback(progress)
            
            # Extract version information from downloaded APK
            if not download_version:
                version_name, version_code = self.extract_apk_version(temp_path)
            else:
                version_name = download_version
                version_code = "0"
                logger.info(f"Using provided version: {version_name}")
            
            # If we still don't have a good version, try to get it from the APK content
            if not self._is_valid_version(version_name):
                logger.warning(f"Invalid version '{version_name}', attempting deeper analysis...")
                
                # Try to extract from APK content more aggressively
                try:
                    extracted_version = await self._deep_version_analysis(temp_path)
                    if extracted_version and self._is_valid_version(extracted_version):
                        version_name = extracted_version
                        logger.info(f"Deep analysis found version: {version_name}")
                except Exception as e:
                    logger.debug(f"Deep analysis failed: {e}")
            
            # If we still don't have a valid version, ask user or use current date
            if not self._is_valid_version(version_name):
                # Check if there's a pattern in the download URL
                url_version = re.search(r'(\d+\.\d+(?:\.\d+)?)', self.config.download_url)
                if url_version and self._is_valid_version(url_version.group(1)):
                    version_name = url_version.group(1)
                    logger.info(f"Found version in download URL: {version_name}")
                else:
                    # Use today's date as fallback (better than timestamp)
                    today = datetime.datetime.now()
                    version_name = f"{today.year % 100}.{today.month}.{today.day}"  # 25.8.3 format
                    logger.warning(f"Using date-based version: {version_name}")
            
            logger.info(f"Final determined version: {version_name} (code: {version_code})")
            
            # Generate versioned filename
            versioned_filename = self.get_versioned_filename(version_name, version_code)
            final_path = self.config.apk_dir / versioned_filename
            
            # Check if this exact version already exists
            if final_path.exists():
                logger.warning(f"Version {version_name} already exists, checking if different...")
                
                # Compare file sizes to see if it's actually different
                existing_size = final_path.stat().st_size
                new_size = temp_path.stat().st_size
                
                if abs(existing_size - new_size) < 1024:  # Less than 1KB difference
                    logger.info(f"Same version and size, keeping existing file")
                    temp_path.unlink()
                    if backup_path and backup_path.exists():
                        backup_path.unlink()
                    return True, final_path
                else:
                    logger.info(f"Same version but different size, updating file")
                    final_path.unlink()
            
            # Move temp file to final versioned location
            temp_path.replace(final_path)
            
            logger.info(f"Successfully downloaded MapWorld APK v{version_name} ({downloaded} bytes)")
            
            # Cleanup old versions
            self.cleanup_old_versions()
            
            # Remove backup file if download was successful
            if backup_path and backup_path.exists():
                backup_path.unlink()
                logger.debug("Removed backup file after successful download")
            
            await self._notify_update_downloaded("MapWorld", version_name)
            return True, final_path
            
        except Exception as e:
            logger.error(f"Download failed: {e}")
            
            # Clean up temp file if it exists
            if temp_path and temp_path.exists():
                temp_path.unlink()
            
            # Restore backup if download failed
            if backup_path and backup_path.exists():
                try:
                    current_apk = self.get_current_apk_path()
                    if current_apk:
                        backup_path.replace(current_apk)
                        logger.info("Restored backup after failed download")
                except Exception as restore_error:
                    logger.error(f"Error restoring backup: {restore_error}")
            
            return False, None
    
    async def _deep_version_analysis(self, apk_path: Path) -> Optional[str]:
        """Deeper analysis of APK for version information"""
        try:
            with zipfile.ZipFile(apk_path, 'r') as zip_file:
                # Search in META-INF/MANIFEST.MF
                try:
                    manifest_mf = zip_file.read('META-INF/MANIFEST.MF').decode('utf-8')
                    version_match = re.search(r'Implementation-Version:\s*([0-9]+\.[0-9]+(?:\.[0-9]+)?)', manifest_mf)
                    if version_match:
                        return version_match.group(1)
                except:
                    pass
                
                # Search in resources.arsc or other config files
                for file_name in zip_file.namelist():
                    if any(keyword in file_name.lower() for keyword in ['version', 'config', 'build']):
                        try:
                            if file_name.endswith(('.xml', '.txt', '.json', '.properties')):
                                content = zip_file.read(file_name).decode('utf-8', errors='ignore')
                                # Search for various version patterns
                                patterns = [
                                    r'"version":\s*"([0-9]+\.[0-9]+(?:\.[0-9]+)?)"',
                                    r'version=([0-9]+\.[0-9]+(?:\.[0-9]+)?)',
                                    r'app_version=([0-9]+\.[0-9]+(?:\.[0-9]+)?)',
                                    r'<version>([0-9]+\.[0-9]+(?:\.[0-9]+)?)</version>',
                                ]
                                for pattern in patterns:
                                    match = re.search(pattern, content, re.IGNORECASE)
                                    if match and self._is_valid_version(match.group(1)):
                                        return match.group(1)
                        except:
                            continue
            
            return None
        except Exception:
            return None

    async def get_installed_version(self, device_ip: str) -> Tuple[Optional[str], Optional[str]]:
        """Determines the installed MapWorld version on a device"""
        try:
            # Check ADB connection first
            connected, error = await self._check_adb_connection_async(device_ip)
            if not connected:
                logger.warning(f"Cannot check version on {device_ip}: {error}")
                return None, None
            
            # Method 1: Try to get version via dumpsys
            result = await asyncio.get_event_loop().run_in_executor(
                None,
                lambda: adb_pool.execute_command(
                    device_ip,
                    ["adb", "shell", f"dumpsys package {self.config.package_name} | grep versionName"]
                )
            )
            
            if result.returncode == 0 and result.stdout:
                # Parse version from output like "versionName=2.54"
                for line in result.stdout.split('\n'):
                    if 'versionName=' in line:
                        version_name = line.split('versionName=')[1].strip()
                        logger.debug(f"Found installed version on {device_ip}: {version_name}")
                        return version_name, None
            
            # Method 2: Try pm list with version
            result = await asyncio.get_event_loop().run_in_executor(
                None,
                lambda: adb_pool.execute_command(
                    device_ip,
                    ["adb", "shell", f"pm dump {self.config.package_name} | grep versionName"]
                )
            )
            
            if result.returncode == 0 and result.stdout:
                for line in result.stdout.split('\n'):
                    if 'versionName=' in line:
                        version_name = line.split('versionName=')[1].strip()
                        logger.debug(f"Found installed version via pm dump on {device_ip}: {version_name}")
                        return version_name, None
            
            # Method 3: Check if package exists at all
            result = await asyncio.get_event_loop().run_in_executor(
                None,
                lambda: adb_pool.execute_command(
                    device_ip,
                    ["adb", "shell", f"pm list packages | grep {self.config.package_name}"]
                )
            )
            
            if result.returncode == 0 and result.stdout and self.config.package_name in result.stdout:
                logger.debug(f"Package found on {device_ip}, but version extraction failed")
                return "unknown", None
            
            logger.info(f"MapWorld (package: {self.config.package_name}) not installed on {device_ip}")
            return None, None
            
        except Exception as e:
            logger.error(f"Error checking installed version on {device_ip}: {e}")
            return None, None
    
    def compare_versions(self, version1: str, version2: str) -> int:
        """Compares two version numbers. Returns -1, 0, or 1"""
        try:
            def normalize_version(v):
                # Split version into parts and convert to integers
                parts = []
                for part in v.split('.'):
                    # Extract numeric part (ignore non-numeric suffixes)
                    numeric_part = ''.join(c for c in part if c.isdigit())
                    parts.append(int(numeric_part) if numeric_part else 0)
                return parts
            
            v1_parts = normalize_version(version1)
            v2_parts = normalize_version(version2)
            
            # Pad shorter version with zeros
            max_len = max(len(v1_parts), len(v2_parts))
            v1_parts.extend([0] * (max_len - len(v1_parts)))
            v2_parts.extend([0] * (max_len - len(v2_parts)))
            
            for i in range(max_len):
                if v1_parts[i] < v2_parts[i]:
                    return -1
                elif v1_parts[i] > v2_parts[i]:
                    return 1
            
            return 0
            
        except Exception as e:
            logger.error(f"Error comparing versions {version1} vs {version2}: {e}")
            return 0  # Treat as equal if comparison fails

    async def should_update_device(self, device_ip: str, new_version: str) -> Tuple[bool, str]:
        """Checks if an update is needed on the device"""
        try:
            installed_version, _ = await self.get_installed_version(device_ip)
            
            if installed_version is None:
                return True, "MapWorld not installed"
            
            if installed_version == "unknown":
                return True, "Cannot determine installed version"
            
            comparison = self.compare_versions(installed_version, new_version)
            
            if comparison < 0:
                return True, f"Update available: {installed_version} → {new_version}"
            elif comparison == 0:
                return False, f"Same version already installed: {installed_version}"
            else:
                return False, f"Newer version already installed: {installed_version} > {new_version}"
                
        except Exception as e:
            logger.error(f"Error checking if update needed for {device_ip}: {e}")
            return True, f"Error checking version, will attempt update: {str(e)}"

    async def install_mapworld(self, device_ip: str, force_install: bool = False) -> bool:
        """Optimized installation with version checking and better error handling"""
        try:
            # Get the latest APK
            current_apk = self.get_current_apk_path()
            if not current_apk or not current_apk.exists():
                logger.error("No APK file found for installation")
                return False
            
            # Extract version info for comparison
            version_name, version_code = self.extract_apk_version(current_apk)
            
            # Check if update is needed (unless forced)
            if not force_install:
                should_update, reason = await self.should_update_device(device_ip, version_name)
                if not should_update:
                    logger.info(f"Skipping installation on {device_ip}: {reason}")
                    return True  # Return True as it's not an error
                logger.info(f"Installing on {device_ip}: {reason}")
            
            device_details = get_device_details(device_ip)
            device_name = device_details.get("display_name", device_ip.split(":")[0])
            
            # Check ADB connection first
            connected, error = await self._check_adb_connection_async(device_ip)
            if not connected:
                logger.warning(f"Skipping installation on {device_ip}: {error}")
                return False
            
            # Execute installation command using synchronous method
            result = await asyncio.get_event_loop().run_in_executor(
                None,
                lambda: adb_pool.execute_command(
                    device_ip,
                    ["adb", "install", "-r", str(current_apk)]
                )
            )
            
            if result.returncode == 0:
                logger.info(f"Successfully installed MapWorld v{version_name} on {device_ip}")
                await self._notify_update_installed(device_name, device_ip, "MapWorld", version_name)
                return True
            else:
                logger.error(f"Installation failed on {device_ip}: {result.stderr}")
                return False
                
        except Exception as e:
            logger.error(f"Installation error on {device_ip}: {e}")
            return False

    def get_version_info(self) -> Dict:
        """Returns information about available versions"""
        versions = self.get_all_apk_versions()
        current_apk = self.get_current_apk_path()
        
        info = {
            "total_versions": len(versions),
            "versions": [],
            "current_version": None
        }
        
        for apk_path, version_name, version_code in versions:
            version_info = {
                "path": str(apk_path),
                "filename": apk_path.name,
                "version_name": version_name,
                "version_code": version_code,
                "size_mb": round(apk_path.stat().st_size / (1024 * 1024), 2),
                "modified": datetime.datetime.fromtimestamp(apk_path.stat().st_mtime).isoformat(),
                "is_current": apk_path == current_apk
            }
            info["versions"].append(version_info)
            
            if apk_path == current_apk:
                info["current_version"] = version_info
        
        return info

    async def _check_adb_connection_async(self, device_ip: str) -> Tuple[bool, str]:
        """Async wrapper for ADB connection check"""
        return await asyncio.get_event_loop().run_in_executor(
            None, check_adb_connection, device_ip
        )

    async def _notify_update_downloaded(self, app_name: str, version: str):
        """Async notification wrapper"""
        await notify_update_downloaded(app_name, version)

    async def _notify_update_installed(self, device_name: str, device_ip: str, app_name: str, version: str):
        """Async notification wrapper"""
        await notify_update_installed(device_name, device_ip, app_name, version)

# Optimized Update Task
async def mapworld_update_task():
    """Robust Auto-Update Task with version management and better error handling"""
    updater = MapWorldUpdater()
    startup_delay = 30
    
    logger.info(f"MapWorld update task starting in {startup_delay} seconds...")
    await asyncio.sleep(startup_delay)
    
    # Log initial version info
    version_info = updater.get_version_info()
    if version_info["current_version"]:
        current = version_info["current_version"]
        logger.info(f"Current MapWorld version: {current['version_name']} ({current['filename']})")
    else:
        logger.info("No MapWorld APK found")
    
    while True:
        try:
            update_available, reason = await updater.has_update_available()
            logger.info(f"Update check result: {reason}")
            
            if update_available:
                logger.info("New MapWorld version available, starting download...")
                
                # Download with progress logging
                async def log_progress(progress):
                    if progress % 10 == 0:  # Log every 10%
                        logger.info(f"Download progress: {progress:.1f}%")
                
                download_success, apk_path = await updater.download_mapworld(log_progress)
                if not download_success:
                    logger.error("Download failed, skipping installation")
                    continue
                
                # Log new version info
                if apk_path:
                    version_name, version_code = updater.extract_apk_version(apk_path)
                    logger.info(f"Successfully downloaded MapWorld v{version_name} (code: {version_code})")
                
                # Install on all connected devices
                config = load_config()
                devices = config.get("devices", [])
                
                if not devices:
                    logger.warning("No devices configured for installation")
                    continue
                
                # Parallel installation with limited concurrency and better reporting
                semaphore = asyncio.Semaphore(3)  # Max 3 concurrent installations
                
                async def install_on_device_with_info(device):
                    async with semaphore:
                        device_ip = device["ip"]
                        device_name = device.get("name", device_ip.split(":")[0])
                        
                        try:
                            # Check current installed version first
                            installed_version, _ = await updater.get_installed_version(device_ip)
                            logger.info(f"Device {device_name} ({device_ip}): "
                                      f"installed={installed_version or 'Not installed'}")
                            
                            result = await updater.install_mapworld(device_ip)
                            
                            if result:
                                final_version, _ = await updater.get_installed_version(device_ip)
                                logger.info(f"Device {device_name}: Installation successful, "
                                          f"now running v{final_version or 'unknown'}")
                            else:
                                logger.warning(f"Device {device_name}: Installation failed")
                            
                            return result
                            
                        except Exception as e:
                            logger.error(f"Device {device_name}: Installation error: {e}")
                            return False
                
                # Execute installations
                tasks = [install_on_device_with_info(device) for device in devices]
                results = await asyncio.gather(*tasks, return_exceptions=True)
                
                # Count results
                successful_installs = 0
                skipped_installs = 0
                failed_installs = 0
                
                for i, result in enumerate(results):
                    if isinstance(result, Exception):
                        failed_installs += 1
                        logger.error(f"Device {devices[i]['ip']}: Exception during installation: {result}")
                    elif result is True:
                        successful_installs += 1
                    elif result is False:
                        failed_installs += 1
                    else:
                        skipped_installs += 1
                
                total_devices = len(devices)
                logger.info(f"Installation summary: {successful_installs} successful, "
                          f"{skipped_installs} skipped, {failed_installs} failed "
                          f"out of {total_devices} devices")
                
                # Log final version status
                final_version_info = updater.get_version_info()
                logger.info(f"Available versions: {final_version_info['total_versions']}")
        
        except Exception as e:
            logger.error(f"Auto-update error: {e}")
            import traceback
            traceback.print_exc()
        
        # Wait for next check
        check_interval = updater.config.check_interval_hours * 3600
        logger.debug(f"Next update check in {updater.config.check_interval_hours} hours")
        await asyncio.sleep(check_interval)

# Optimized Scheduled Task
async def scheduled_update_task():
    """
    Improved scheduled update checks with flexible configuration
    """
    # Configurable update times
    update_hours = [3, 15]  # 3:00 AM and 3:00 PM
    last_run_dates = set()
    
    while True:
        try:
            now = datetime.datetime.now()
            today = now.date()
            current_hour = now.hour
            
            # Check if it's time for an update check
            should_run = (
                current_hour in update_hours and 
                now.minute < 5 and  # Within first 5 minutes of the hour
                (today, current_hour) not in last_run_dates
            )
            
            if should_run:
                logger.info(f"Running scheduled update check at {now}")
                
                # MapWorld Updates
                updater = MapWorldUpdater()
                update_available, reason = await updater.has_update_available()
                
                if update_available:
                    logger.info(f"Scheduled update triggered: {reason}")
                    download_success, apk_path = await updater.download_mapworld()
                    
                    if download_success and apk_path:
                        version_name, version_code = updater.extract_apk_version(apk_path)
                        logger.info(f"Scheduled download completed: MapWorld v{version_name}")
                    else:
                        logger.error("Scheduled download failed")
                
                # PoGO Updates (existing function)
                ensure_latest_apk_downloaded()
                
                # Mark this hour as completed for today
                last_run_dates.add((today, current_hour))
                
                # Clean up old entries (keep only last 7 days)
                cutoff_date = today - datetime.timedelta(days=7)
                last_run_dates = {
                    (date, hour) for date, hour in last_run_dates 
                    if date >= cutoff_date
                }
                
                logger.info("Scheduled update check completed")
            
            # Check every minute
            await asyncio.sleep(60)
            
        except Exception as e:
            logger.error(f"Error in scheduled update task: {e}")
            import traceback
            traceback.print_exc()
            await asyncio.sleep(300)  # Wait 5 minutes on error

async def check_all_device_versions() -> Dict:
    """Checks MapWorld versions on all configured devices"""
    updater = MapWorldUpdater()
    config = load_config()
    devices = config.get("devices", [])
    
    if not devices:
        return {"error": "No devices configured"}
    
    results = {}
    
    async def check_device_version(device):
        device_ip = device["ip"]
        device_name = device.get("name", device_ip.split(":")[0])
        
        try:
            installed_version, _ = await updater.get_installed_version(device_ip)
            connected, connection_error = await updater._check_adb_connection_async(device_ip)
            
            return {
                "device_name": device_name,
                "device_ip": device_ip,
                "installed_version": installed_version,
                "connected": connected,
                "connection_error": connection_error if not connected else None,
                "status": "installed" if installed_version else "not_installed"
            }
        except Exception as e:
            return {
                "device_name": device_name,
                "device_ip": device_ip,
                "installed_version": None,
                "connected": False,
                "connection_error": str(e),
                "status": "error"
            }
    
    # Check all devices in parallel
    tasks = [check_device_version(device) for device in devices]
    device_results = await asyncio.gather(*tasks)
    
    # Get current downloadable version
    current_apk = updater.get_current_apk_path()
    available_version = None
    if current_apk and current_apk.exists():
        available_version, _ = updater.extract_apk_version(current_apk)
    
    # Organize results
    for device_result in device_results:
        device_ip = device_result["device_ip"]
        results[device_ip] = device_result
        
        # Add update status
        if available_version and device_result["installed_version"]:
            if device_result["installed_version"] != "unknown":
                comparison = updater.compare_versions(
                    device_result["installed_version"], 
                    available_version
                )
                if comparison < 0:
                    device_result["update_available"] = True
                    device_result["update_info"] = f"{device_result['installed_version']} → {available_version}"
                elif comparison == 0:
                    device_result["update_available"] = False
                    device_result["update_info"] = "Up to date"
                else:
                    device_result["update_available"] = False
                    device_result["update_info"] = f"Newer version installed: {device_result['installed_version']}"
            else:
                device_result["update_available"] = True
                device_result["update_info"] = "Version unknown, update recommended"
        elif available_version:
            device_result["update_available"] = True
            device_result["update_info"] = f"Not installed, can install v{available_version}"
        else:
            device_result["update_available"] = False
            device_result["update_info"] = "No APK available for installation"
    
    # Add summary
    total_devices = len(device_results)
    connected_devices = sum(1 for r in device_results if r["connected"])
    installed_devices = sum(1 for r in device_results if r["status"] == "installed")
    update_needed = sum(1 for r in device_results if r.get("update_available", False))
    
    summary = {
        "total_devices": total_devices,
        "connected_devices": connected_devices,
        "installed_devices": installed_devices,
        "updates_needed": update_needed,
        "available_version": available_version,
        "devices": results
    }
    
    return summary

# Helper functions for version management
def get_mapworld_version_info() -> Dict:
    """Public function to retrieve version information"""
    updater = MapWorldUpdater()
    return updater.get_version_info()

async def install_specific_version(device_ip: str, version_name: str = None) -> bool:
    """Installs a specific version on a device"""
    updater = MapWorldUpdater()
    
    if version_name:
        # Search for specific version
        versions = updater.get_all_apk_versions()
        target_apk = None
        
        for apk_path, v_name, v_code in versions:
            if v_name == version_name:
                target_apk = apk_path
                break
        
        if not target_apk:
            logger.error(f"Version {version_name} not found")
            return False
        
        # Temporarily set APK as "current" for installation
        current_apk = updater.get_current_apk_path()
        if current_apk != target_apk:
            # Backup current
            backup_name = f"{current_apk.stem}_temp_backup{current_apk.suffix}"
            backup_path = current_apk.parent / backup_name
            if current_apk and current_apk.exists():
                shutil.copy2(current_apk, backup_path)
            
            # Copy target to current position
            temp_current = current_apk.parent / f"temp_current_{target_apk.name}"
            shutil.copy2(target_apk, temp_current)
            
            try:
                result = await updater.install_mapworld(device_ip)
                
                # Restore original current
                if backup_path.exists():
                    backup_path.replace(current_apk)
                    backup_path.unlink(missing_ok=True)
                
                temp_current.unlink(missing_ok=True)
                return result
                
            except Exception as e:
                # Cleanup on error
                temp_current.unlink(missing_ok=True)
                if backup_path.exists():
                    backup_path.replace(current_apk)
                raise e
    
    # Install current version
    return await updater.install_mapworld(device_ip)

def cleanup_mapworld_versions(keep_versions: int = None) -> int:
    """Manual cleanup of old versions"""
    updater = MapWorldUpdater()
    
    if keep_versions is not None:
        original_keep = updater.config.keep_previous_versions
        updater.config.keep_previous_versions = keep_versions
        
    try:
        versions_before = len(updater.get_all_apk_versions())
        updater.cleanup_old_versions()
        versions_after = len(updater.get_all_apk_versions())
        
        removed_count = versions_before - versions_after
        logger.info(f"Cleanup completed: removed {removed_count} old versions")
        return removed_count
        
    finally:
        if keep_versions is not None:
            updater.config.keep_previous_versions = original_keep

def fix_apk_version(current_filename: str, correct_version: str) -> bool:
    """Renames an APK file with the correct version"""
    try:
        updater = MapWorldUpdater()
        current_path = updater.config.apk_dir / current_filename
        
        if not current_path.exists():
            logger.error(f"File {current_filename} not found")
            return False
        
        # Validate new version
        if not updater._is_valid_version(correct_version):
            logger.error(f"Invalid version format: {correct_version}")
            return False
        
        # Create new filename
        new_filename = updater.get_versioned_filename(correct_version, "0")
        new_path = updater.config.apk_dir / new_filename
        
        if new_path.exists():
            logger.warning(f"Target filename {new_filename} already exists")
            return False
        
        # Rename
        current_path.rename(new_path)
        logger.info(f"Renamed {current_filename} → {new_filename}")
        
        return True
        
    except Exception as e:
        logger.error(f"Error renaming APK: {e}")
        return False

async def force_download_with_version(version: str) -> bool:
    """Downloads MapWorld and forces a specific version"""
    try:
        updater = MapWorldUpdater()
        
        logger.info(f"Force downloading MapWorld with version {version}")
        success, apk_path = await updater.download_mapworld(force_version=version)
        
        if success and apk_path:
            logger.info(f"Successfully downloaded and set version to {version}")
            return True
        else:
            logger.error("Force download failed")
            return False
            
    except Exception as e:
        logger.error(f"Error during force download: {e}")
        return False

def debug_apk_version(filename: str = None) -> None:
    """Debug function to find all versions in an APK"""
    try:
        updater = MapWorldUpdater()
        
        if filename:
            apk_path = updater.config.apk_dir / filename
        else:
            apk_path = updater.get_current_apk_path()
        
        if not apk_path or not apk_path.exists():
            print(f"APK file not found: {apk_path}")
            return
        
        print(f"\n=== DEBUG: Analyzing {apk_path.name} ===")
        
        # Enable debug mode
        version, code = updater.extract_apk_version(apk_path, debug=True)
        
        print(f"\nFinal result: {version} (code: {code})")
        
    except Exception as e:
        print(f"Error during debug analysis: {e}")

def quick_fix_version() -> bool:
    """Quick repair of current version to 2.55"""
    try:
        updater = MapWorldUpdater()
        current_apk = updater.get_current_apk_path()
        
        if not current_apk:
            logger.error("No current APK found")
            return False
        
        # Correct to probably right version
        correct_version = "2.55"  # Adjustable based on current MapWorld version
        
        new_filename = updater.get_versioned_filename(correct_version, "0")
        new_path = current_apk.parent / new_filename
        
        if new_path.exists():
            logger.warning(f"Target file {new_filename} already exists, removing old file")
            current_apk.unlink()
        else:
            current_apk.rename(new_path)
        
        logger.info(f"Fixed version: {current_apk.name} → {new_filename}")
        return True
        
    except Exception as e:
        logger.error(f"Error fixing version: {e}")
        return False

async def redownload_with_correct_version(correct_version: str = "2.55") -> bool:
    """Downloads MapWorld again and forces correct version"""
    try:
        updater = MapWorldUpdater()
        backup_path = None
        
        # Backup current if exists
        current_apk = updater.get_current_apk_path()
        if current_apk:
            backup_path = current_apk.with_suffix('.backup')
            current_apk.rename(backup_path)
            logger.info(f"Backed up current APK to {backup_path.name}")
        
        # Download with correct version
        logger.info(f"Re-downloading MapWorld with correct version {correct_version}")
        success, new_path = await updater.download_mapworld(force_version=correct_version)
        
        if success:
            logger.info(f"Successfully re-downloaded with version {correct_version}")
            
            # Remove backup if successful
            if backup_path and backup_path.exists():
                backup_path.unlink()
                logger.info("Removed backup file")
            
            return True
        else:
            logger.error("Re-download failed")
            
            # Restore backup
            if backup_path and backup_path.exists():
                backup_path.rename(current_apk)
                logger.info("Restored backup file")
            
            return False
            
    except Exception as e:
        logger.error(f"Error during re-download: {e}")
        return False

def list_mapworld_versions() -> None:
    """Shows all available MapWorld versions"""
    try:
        updater = MapWorldUpdater()
        info = updater.get_version_info()
        
        print(f"\n=== MapWorld Versions ({info['total_versions']} total) ===")
        
        for i, version in enumerate(info['versions']):
            status = " [CURRENT]" if version['is_current'] else ""
            print(f"{i+1:2d}. {version['filename']}{status}")
            print(f"    Version: {version['version_name']} (code: {version['version_code']})")
            print(f"    Size: {version['size_mb']} MB")
            print(f"    Modified: {version['modified']}")
            print()
        
        if info['current_version']:
            print(f"Current version: {info['current_version']['version_name']}")
        else:
            print("No current version found")
            
    except Exception as e:
        print(f"Error listing versions: {e}")
            
# PIF Version Management Functions
PIF_MODULE_DIR = BASE_DIR / "data" / "modules" / "playintegrityfork"
PIFIX_MODULE_DIR = BASE_DIR / "data" / "modules" / "playintegrityfix"
PIF_GITHUB_API = "https://api.github.com/repos/osm0sis/PlayIntegrityFork/releases?per_page=10"
PIFIX_GITHUB_API = "https://api.github.com/repos/andi2022/PlayIntegrityFix/releases?per_page=10"

def get_preferred_module_type():
    """Gets the user's preferred module type from config"""
    config = load_config()
    return config.get("preferred_module_type", "fork")

def save_module_preference(module_type):
    """Saves the preferred module type to config"""
    config = load_config()
    config["preferred_module_type"] = module_type
    save_config(config)
    return config

# GitHub API cache for module versions
github_api_cache = {}
GITHUB_CACHE_TTL = 3600  # 1 hour cache

def clear_github_api_cache():
    """Clears the GitHub API cache to force fresh data on next request"""
    global github_api_cache
    github_api_cache.clear()
    print("GitHub API cache cleared")

async def fetch_available_module_versions(module_type="fork"):
    """Fetches available module versions from GitHub API with caching to reduce rate limiting"""
    # Check cache first
    cache_key = f"module_versions_{module_type}"
    current_time = time.time()
    
    if cache_key in github_api_cache:
        cached_data, timestamp = github_api_cache[cache_key]
        if current_time - timestamp < GITHUB_CACHE_TTL:
            print(f"Using cached {module_type.upper()} versions (cached {int((current_time - timestamp)/60)} minutes ago)")
            return cached_data
    if module_type == "fix":
        api_url = PIFIX_GITHUB_API
        module_dir = PIFIX_MODULE_DIR
    else:
        api_url = PIF_GITHUB_API
        module_dir = PIF_MODULE_DIR
    
    module_dir.mkdir(parents=True, exist_ok=True)
    
    # Retry configuration
    max_retries = 3
    timeout_values = [10, 15, 20]  # Progressive timeout
    
    for attempt in range(max_retries):
        try:
            timeout = timeout_values[attempt]
            print(f"Fetching {module_type.upper()} releases from GitHub API (attempt {attempt + 1}/{max_retries})...")
            
            async with httpx.AsyncClient(
                follow_redirects=True,
                timeout=httpx.Timeout(timeout),
                limits=httpx.Limits(max_connections=5)
            ) as client:
                
                headers = {
                    "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36",
                    "Accept": "application/vnd.github.v3+json",
                    "X-GitHub-Api-Version": "2022-11-28"
                }
                
                response = await client.get(api_url, headers=headers)
                
                # Handle different HTTP status codes
                if response.status_code == 200:
                    try:
                        releases = response.json()
                        if not releases or not isinstance(releases, list):
                            print(f"Empty or invalid releases data on attempt {attempt + 1}")
                            if attempt < max_retries - 1:
                                await asyncio.sleep(2 ** attempt)  # Exponential backoff
                                continue
                            return []
                        
                        versions = []
                        for release in releases:
                            if not isinstance(release, dict):
                                continue
                                
                            tag_name = release.get("tag_name", "").strip()
                            if not tag_name:
                                continue
                                
                            version = tag_name.lstrip("v")
                            published_at = release.get("published_at", "")
                            
                            # Find zip asset with validation
                            assets = release.get("assets", [])
                            if not isinstance(assets, list):
                                continue
                                
                            zip_asset = next(
                                (asset for asset in assets
                                 if isinstance(asset, dict) and 
                                 asset.get("name", "").endswith(".zip") and
                                 asset.get("browser_download_url")),
                                None
                            )
                            
                            if zip_asset:
                                versions.append({
                                    "version": version,
                                    "tag_name": tag_name,
                                    "published_at": published_at,
                                    "download_url": zip_asset.get("browser_download_url"),
                                    "filename": zip_asset.get("name"),
                                    "module_type": module_type
                                })
                        
                        if versions:
                            versions.sort(key=lambda x: parse_version(x["version"]), reverse=True)
                            print(f"Successfully fetched {len(versions)} {module_type.upper()} versions")
                            # Cache the successful result
                            github_api_cache[cache_key] = (versions, current_time)
                            return versions
                        else:
                            print(f"No valid releases found on attempt {attempt + 1}")
                            
                    except (json.JSONDecodeError, KeyError, TypeError) as e:
                        print(f"Invalid API response format on attempt {attempt + 1}: {str(e)}")
                        
                elif response.status_code == 403:
                    print(f"GitHub API rate limit exceeded (attempt {attempt + 1})")
                    if attempt < max_retries - 1:
                        print("Waiting 5 minutes before retry to respect rate limit (60 requests per hour)...")
                        await asyncio.sleep(300)  # Wait 5 minutes for rate limit reset
                        continue
                        
                elif response.status_code == 404:
                    print(f"GitHub repository not found: {api_url}")
                    return []  # Don't retry for 404
                    
                else:
                    print(f"GitHub API HTTP {response.status_code} on attempt {attempt + 1}")
                
        except (httpx.TimeoutException, httpx.ConnectTimeout, httpx.ReadTimeout) as e:
            print(f"Network timeout on attempt {attempt + 1}: {str(e)}")
        except (httpx.HTTPError, httpx.RequestError) as e:
            print(f"Network error on attempt {attempt + 1}: {str(e)}")
        except Exception as e:
            print(f"Unexpected error on attempt {attempt + 1}: {str(e)}")
        
        # Wait before retry (except on last attempt)
        if attempt < max_retries - 1:
            wait_time = 2 ** attempt
            print(f"Retrying in {wait_time} seconds...")
            await asyncio.sleep(wait_time)
    
    print(f"Failed to fetch {module_type.upper()} versions after {max_retries} attempts")
    return []

async def fetch_available_pif_versions():
    """
    Compatibility function to maintain backward compatibility with existing code.
    Simply calls fetch_available_module_versions with 'fork' as the module type.
    """
    return await fetch_available_module_versions("fork")

async def download_module_version(version_info):
    """Downloads a module version and saves it with the original filename"""
    try:
        version = version_info["version"]
        download_url = version_info["download_url"]
        filename = version_info["filename"]
        module_type = version_info.get("module_type", "fork")
        
        if module_type == "fix":
            module_dir = PIFIX_MODULE_DIR
        else:
            module_dir = PIF_MODULE_DIR
            
        module_path = module_dir / filename
        
        if module_path.exists():
            print(f"{module_type.upper()} version {version} already downloaded at {module_path}")
            return module_path
        
        print(f"Downloading {module_type.upper()} version {version} from {download_url}")
        async with httpx.AsyncClient(follow_redirects=True) as client:
            headers = {
                "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/91.0.4472.124 Safari/537.36",
                "Accept": "application/octet-stream",
                "Accept-Encoding": "gzip, deflate, br"
            }
            
            download_response = await client.get(download_url, headers=headers, timeout=30)
            
            if download_response.status_code != 200:
                print(f"Download failed with status code: {download_response.status_code}")
                return None
                
            content_type = download_response.headers.get("content-type", "").lower()
            if "html" in content_type:
                print(f"GitHub returned HTML instead of ZIP file. Using alternative download method...")
                
                if module_type == "fix":
                    direct_url = download_url.replace("/api.github.com/repos/", "/github.com/")
                    direct_url = direct_url.replace("/releases/assets/", "/releases/download/v")
                else:
                    direct_url = download_url.replace("/api.github.com/repos/", "/github.com/")
                    direct_url = direct_url.replace("/releases/assets/", "/releases/download/v")
                
                direct_url = direct_url.replace("/download/v", "/download/v" + version + "/")
                
                print(f"Trying alternative URL: {direct_url}")
                alt_response = await client.get(direct_url, headers=headers, timeout=30)
                
                if alt_response.status_code != 200:
                    print(f"Alternative download failed with status code: {alt_response.status_code}")
                    return None
                    
                content_type = alt_response.headers.get("content-type", "").lower()
                if "html" in content_type:
                    print(f"Alternative method also returned HTML. Unable to download ZIP file.")
                    return None
                    
                download_response = alt_response
            
            with open(module_path, "wb") as f:
                f.write(download_response.content)
            
            if not zipfile.is_zipfile(module_path):
                print("Downloaded file is not a valid ZIP")
                module_path.unlink()
                return None
        
        print(f"Successfully downloaded {module_type.upper()} version {version} to {module_path}")
        return module_path
        
    except Exception as e:
        print(f"Error downloading {version_info.get('module_type', 'fork').upper()} version {version}: {str(e)}")
        traceback.print_exc()
        return None

async def get_all_module_versions_for_ui():
    """Returns combined module versions for UI display"""
    fork_versions = await fetch_available_module_versions("fork")
    fix_versions = await fetch_available_module_versions("fix")
    
    for version in fork_versions:
        version["name"] = f"PlayIntegrityFork {version['version']}"
    for version in fix_versions:
        version["name"] = f"PlayIntegrityFix {version['version']}"
    
    combined_versions = fork_versions + fix_versions
    combined_versions.sort(key=lambda x: x["published_at"], reverse=True)
    
    return {
        "all": combined_versions,
        "fork": fork_versions,
        "fix": fix_versions,
        "preferred": get_preferred_module_type()
    }

async def get_pif_versions_for_ui():
    """
    Compatibility function for code that uses get_pif_versions_for_ui.
    Returns versions based on the preferred module type.
    """
    config = load_config()
    preferred_module = config.get("preferred_module_type", "fork")
    
    versions = await fetch_available_module_versions(preferred_module)
    
    versions.sort(key=lambda x: parse_version(x["version"]), reverse=True)
    return versions

async def fetch_pif_version(version_info):
    """Compatibility wrapper for download_module_version"""
    return await download_module_version(version_info)

async def install_pif_module(device_ip: str, pif_module_path=None):
    """Compatibility wrapper for install_module_with_progress"""
    return await install_module_with_progress(device_ip, pif_module_path, "fork")

# Optimized Module Update Task
async def optimized_module_update_task():
    """Checks and installs module updates with reduced version queries"""
    while True:
        try:
            config = load_config()
            
            print("🔍 Checking for PlayIntegrity Module updates...")

            preferred_module = config.get("preferred_module_type", "fork")

            versions = await fetch_available_module_versions(preferred_module)
            if not versions:
                print(f"❌ No valid {preferred_module.upper()} versions available, skipping check.")
                await asyncio.sleep(3 * 3600)
                continue
                
            latest_version = versions[0]
            new_version = latest_version["version"]

            print(f"📌 Latest {preferred_module.upper()} version available: {new_version}")
                
            module_path = await download_module_version(latest_version)
            if not module_path:
                print("Failed to download module, skipping update")
                await asyncio.sleep(3 * 3600)
                continue

            if not config.get("pif_auto_update_enabled", True):
                print(f"{preferred_module.upper()} auto-update is disabled in configuration. Module downloaded but not installed.")
                await asyncio.sleep(3 * 3600)
                continue

            # Manual implementation to find devices needing update
            devices_to_update = []
            config_device_ips = {dev["ip"] for dev in config.get("devices", [])}
            
            for device in config.get("devices", []):
                device_id = device["ip"]
                
                connected, error = check_adb_connection(device_id)
                if not connected:
                    print(f"Device {device_id} not reachable via ADB, skipping update check: {error}")
                    continue
                    
                version_info = version_manager.get_version_info(device_id, force_refresh=False)
                
                if not version_info:
                    print(f"No version information available for {device_id}")
                    continue
                    
                installed_module = version_info.get("module_version", "N/A").strip()
                
                # Determine if update needed
                if installed_module == "N/A":
                    print(f"No Play Integrity module found on {device_id}, will install module")
                    devices_to_update.append(device_id)
                    continue
                    
                module_is_fork = "Fork" in installed_module
                
                if (preferred_module == "fix" and module_is_fork) or (preferred_module == "fork" and not module_is_fork):
                    print(f"Device {device_id} has different module type, switching to {preferred_module.upper()}")
                    devices_to_update.append(device_id)
                    continue
                
                # Extract and compare versions
                if module_is_fork:
                    version_match = re.search(r'Fork\s+v?(\d+(?:\.\d+)?.*|v?\d+)', installed_module)
                else:
                    version_match = re.search(r'Fix\s+v?(\d+(?:\.\d+)?.*|v?\d+)', installed_module)
                    
                if version_match:
                    current_version = version_match.group(1)
                    try:
                        current_tuple = parse_version(current_version)
                        new_tuple = parse_version(new_version)
                        
                        if current_tuple < new_tuple:
                            print(f"Update needed for {device_id}: {current_version} -> {new_version}")
                            devices_to_update.append(device_id)
                    except (ValueError, AttributeError):
                        devices_to_update.append(device_id)
                else:
                    devices_to_update.append(device_id)

            update_count = len(devices_to_update)
            if update_count > 0:
                print(f"🚀 Installing {preferred_module.upper()} version {new_version} on {update_count} devices")
                
                for device_id in devices_to_update:
                    try:
                        print(f"⚡ Updating device {device_id} to {preferred_module.upper()} version {new_version}")
                        await install_module_with_progress(device_id, module_path, preferred_module)
                        
                        # Mark device for version refresh
                        version_manager.mark_for_refresh(device_id)

                    except Exception as e:
                        print(f"Error installing module on {device_id}: {str(e)}")
                
                print(f"✅ {preferred_module.upper()} update complete")
                
                status_data = await get_status_data()
                await ws_manager.broadcast(status_data)
            else:
                print("✅ All devices already have the latest version. No updates needed.")

        except Exception as e:
            print(f"❌ Module Auto-Update Error: {str(e)}")
            import traceback
            traceback.print_exc()

        await asyncio.sleep(3 * 3600)

async def install_module_with_progress(device_ip: str, module_path=None, module_type="fork"):
    """Installs PlayIntegrityFork or PlayIntegrityFix module with progress updates for the UI"""
    global update_in_progress, current_progress
    
    def cleanup_installation():
        """Helper function to clean up installation state"""
        global update_in_progress, current_progress
        update_in_progress = False
        current_progress = 0
        clear_device_update_status(device_ip)
    
    try:
        # Mark device as in update
        mark_device_in_update(device_ip, f"pif-{module_type}")
        
        device_id = format_device_id(device_ip)
        print(f"Starting {module_type.upper()} module installation for {device_ip}")
        
        update_progress(5)
        
        # Verify this device is in the config
        config = load_config()
        device_in_config = any(dev["ip"] == device_id for dev in config.get("devices", []))
        if not device_in_config:
            print(f"Device {device_id} not found in config, aborting module installation")
            cleanup_installation()
            return False
        
        update_progress(10)
        
        if not adb_pool.ensure_connected(device_id):
            print(f"Cannot connect to {device_id} for module installation")
            cleanup_installation()
            return False
        
        if module_path is None or not Path(module_path).exists():
            print(f"Module file not found at {module_path}")
            cleanup_installation()
            return False
        
        version = "unknown"
        filename = Path(module_path).name
        version_match = re.search(r'v?(\d+\.\d+)', filename)
        if version_match:
            version = version_match.group(1)
        
        device_details = get_device_details(device_ip)
        device_name = device_details.get("display_name", device_ip.split(":")[0])

        update_progress(15)
        
        # Remove existing modules (no reboot needed)
        print(f"Removing existing modules on {device_id}")
        adb_pool.execute_command(
            device_id,
            ["adb", "shell", "su -c 'rm -rf /data/adb/modules/playintegrityfix'"]
        )
        adb_pool.execute_command(
            device_id,
            ["adb", "shell", "su -c 'rm -rf /data/adb/modules/playintegrityfork'"]
        )
        
        update_progress(25)
        print(f"Pushing {module_type.upper()} module to {device_id}")
        
        push_result = adb_pool.execute_command(
            device_id,
            ["adb", "push", str(module_path), "/data/local/tmp/pif.zip"]
        )
        
        if push_result.returncode != 0:
            print(f"Failed to push module to device: {push_result.stderr}")
            cleanup_installation()
            return False
        
        update_progress(40)
        print(f"Installing {module_type.upper()} module on {device_id}")
        
        # First check if Magisk is installed and available
        magisk_check = adb_pool.execute_command(
            device_id,
            ["adb", "shell", "su -c 'magisk -v'"]
        )
        
        if magisk_check.returncode != 0 or "not found" in magisk_check.stderr:
            print(f"Magisk not available on device {device_id}: {magisk_check.stderr}")
            cleanup_installation()
            return False
        
        # Now install the module
        install_result = adb_pool.execute_command(
            device_id,
            ["adb", "shell", "su -c 'magisk --install-module /data/local/tmp/pif.zip'"]
        )
        
        if install_result.returncode != 0:
            print(f"Module installation failed: {install_result.stderr}")
            cleanup_installation()
            return False
        
        update_progress(60)
        
        # Verify module was installed
        module_dir = "/data/adb/modules/playintegrityfork" if module_type == "fork" else "/data/adb/modules/playintegrityfix"
        verify_result = adb_pool.execute_command(
            device_id,
            ["adb", "shell", f"su -c 'ls -la {module_dir}'"]
        )
        
        if verify_result.returncode != 0 or "No such file" in verify_result.stderr:
            print(f"Module directory not found after installation: {verify_result.stderr}")
            cleanup_installation()
            return False
        
        # Clean up
        adb_pool.execute_command(
            device_id,
            ["adb", "shell", "rm /data/local/tmp/pif.zip"]
        )
        
        update_progress(70)
        print(f"Rebooting {device_id} to apply {module_type.upper()} module")
        
        adb_pool.execute_command(device_id, ["adb", "reboot"])

        # Wait for device to come back online after reboot
        print(f"Waiting for device {device_id} to come back online after reboot...")
        device_back_online = False
        for i in range(30):  # 5 minutes timeout
            await asyncio.sleep(10)
            update_progress(70 + (i * 0.8))  # Progress from 70 to 94
            try:
                if adb_pool.ensure_connected(device_id):
                    print(f"Device {device_id} is back online after reboot")
                    device_back_online = True
                    break
            except Exception as e:
                print(f"Error checking device connectivity: {str(e)}")
                continue
                
        if not device_back_online:
            print(f"Device {device_id} did not come back online after reboot. Installation status uncertain.")
            cleanup_installation()
            return False
            
        # Verify module is actually enabled
        await asyncio.sleep(10)  # Give a moment for the system to stabilize
        
        update_progress(95)
        
        # Final verification
        final_verify = adb_pool.execute_command(
            device_id,
            ["adb", "shell", f"su -c 'cat {module_dir}/module.prop'"]
        )
        
        if final_verify.returncode != 0 or "No such file" in final_verify.stderr:
            print(f"Module appears to be not properly installed after reboot: {final_verify.stderr}")
            cleanup_installation()
            return False
            
        module_enabled = adb_pool.execute_command(
            device_id,
            ["adb", "shell", f"su -c '[ -f {module_dir}/disable ] && echo disabled || echo enabled'"]
        )
        
        if "disabled" in module_enabled.stdout:
            print(f"Warning: Module is installed but appears to be disabled")
        
        device_status_cache.clear()
        version_manager.mark_for_refresh(device_id)
        print(f"{module_type.upper()} update successfully completed for {device_id}")
        
        # Clear GitHub API cache to ensure fresh version info on next check
        clear_github_api_cache()

        # Now that we've verified installation, send notification
        module_name = "PlayIntegrityFork" if module_type == "fork" else "PlayIntegrityFix"
        await notify_update_installed(device_name, device_id, module_name, version)
        
        status_data = await get_status_data()
        await ws_manager.broadcast(status_data)
        
        update_progress(100)
        await asyncio.sleep(2)
        
        # Successful completion cleanup
        update_in_progress = False
        current_progress = 0
        
        return True
    
    except Exception as e:
        print(f"Module Installation error for {device_ip}: {str(e)}")
        traceback.print_exc()
        cleanup_installation()
        return False
    
    finally:
        # Clear update status
        clear_device_update_status(device_ip)

def parse_version(v: str):
    """
    Parses a version string (e.g. "1.2.3" or "v1.2.3") into a tuple of integers.
    If the string is not correctly formatted, an empty tuple is returned.
    """
    try:
        v = v.strip().lstrip("v")
        parts = []
        for part in v.split('.'):
            if part.isdigit():
                parts.append(int(part))
        
        if not parts:
            return ()
            
        while len(parts) < 3:
            parts.append(0)
        return tuple(parts)
    except Exception as e:
        print(f"Error parsing version '{v}': {e}")
        return ()

# Optimized Device Monitoring
async def optimized_device_monitoring():
    """
    Optimized device monitoring with fixed notification logic to ensure
    both offline and online notifications are properly sent.
    """
    device_last_status = {}  # Track previous status for change detection
    monitoring_interval = 60  # seconds
    notification_cooldown = 300  # seconds (5 minutes) between repeated notifications
    
    while True:
        try:
            config = load_config()
            current_time = time.time()
            
            # Find all devices that should be monitored
            monitored_devices = [
                dev for dev in config.get("devices", [])
                if dev.get("control_enabled", False)
            ]
            
            for device in monitored_devices:
                device_id = device["ip"]
                display_name = device.get("display_name", device_id.split(":")[0])
                
                # Skip devices currently being updated
                if device_id in devices_in_update and devices_in_update[device_id]["in_update"]:
                    update_type = devices_in_update[device_id]["update_type"]
                    update_duration = int(current_time - devices_in_update[device_id]["started_at"])
                    print(f"Device {device_id} is currently undergoing a {update_type} update for {update_duration} seconds - skipping monitoring")
                    continue
                
                # Get current status from the status cache (populated by API updates)
                status = device_status_cache.get(device_id, {})
                if not status:
                    print(f"No status data available for {device_id}, skipping monitoring")
                    continue
                
                # Extract data from the status cache
                is_alive = status.get("is_alive", False)
                mem_free = status.get("mem_free", 0)
                adb_status = status.get("adb_status", False)
                runtime = status.get("runtime", None)
                last_runtime = status.get("last_runtime", None)
                
                # Get notification timestamps to prevent spam
                last_offline_notification = status.get("last_offline_notification", 0)
                last_online_notification = status.get("last_online_notification", 0)
                
                # Get last known status of the device 
                was_alive = device_last_status.get(device_id, {}).get("is_alive")
                
                # If we don't have previous status (first run), assume null state
                if was_alive is None:
                    # Initialize status without sending notifications
                    device_last_status[device_id] = {"is_alive": is_alive}
                    print(f"Initialized status tracking for {device_id}: is_alive={is_alive}")
                    # Store this status in cache without notification
                    status["last_status_change"] = current_time
                    device_status_cache[device_id] = status
                    continue
                
                # Check for status change to send notifications
                # Device just went offline
                if was_alive and not is_alive:
                    # Check if we need to send notification (respect cooldown)
                    if current_time - last_offline_notification > notification_cooldown:
                        print(f"Device {display_name} ({device_id}) went offline - sending notification")
                        await notify_device_offline(display_name, device_id)
                        
                        # Update notification timestamp
                        status["last_offline_notification"] = current_time
                        device_status_cache[device_id] = status
                    else:
                        print(f"Device {display_name} ({device_id}) offline notification in cooldown")
                
                # Device just came back online
                elif not was_alive and is_alive:
                    # Check if we need to send notification (respect cooldown)
                    if current_time - last_online_notification > notification_cooldown:
                        print(f"Device {display_name} ({device_id}) came back online - sending notification")
                        await notify_device_online(display_name, device_id)
                        
                        # Update notification timestamp
                        status["last_online_notification"] = current_time
                        device_status_cache[device_id] = status
                    else:
                        print(f"Device {display_name} ({device_id}) online notification in cooldown")
                
                # Format runtime for display
                runtime_formatted = format_runtime(runtime) if runtime is not None else "N/A"
                last_runtime_formatted = format_runtime(last_runtime) if last_runtime is not None else "N/A"
                
                # Format memory value
                mem_mb = mem_free / 1024 if mem_free > 0 else 0
                
                # Print detailed status information
                status_emoji = "✅" if is_alive else "❌"
                memory_status = f"{mem_mb:.2f} MB / {device.get('memory_threshold', 200)} MB"
                
                # Create detailed status line 
                status_line = (
                    f"Device {display_name} ({device_id}): "
                    f"API Status: {status_emoji} | "
                    f"Memory: {memory_status} | "
                    f"Runtime: {runtime_formatted}"
                )
                
                # Add last runtime if available
                if last_runtime is not None:
                    status_line += f" | Last Runtime: {last_runtime_formatted}"
                    
                print(status_line)
                
                if not adb_status:
                    print(f"  - Device not reachable via ADB, skipping monitoring")
                    continue
                
                # Check if restart is needed
                threshold = device.get("memory_threshold", 200)
                restart_needed = False
                restart_reason = ""
                
                if not is_alive:
                    restart_needed = True
                    restart_reason = "API reports device as offline"
                
                elif mem_free > 0 and mem_free < threshold * 1024:
                    # Restart if memory is below the configured threshold
                    restart_needed = True
                    restart_reason = f"Low memory: {mem_mb:.2f} MB (Threshold: {threshold} MB)"
    
                    # Check notification cooldown for memory restart
                    last_memory_notification = status.get("last_memory_notification", 0)
                    if current_time - last_memory_notification > notification_cooldown:
                        await notify_memory_restart(display_name, device_id, mem_free, threshold)
                        status["last_memory_notification"] = current_time
                        device_status_cache[device_id] = status
                    else:
                        # Memory is below threshold but not critically low
                        print(f"  - Memory is below threshold but not critically low")
                
                # Always check if the device was restarted recently to avoid restart loops
                last_restart_time = status.get("last_restart_time", 0)
                time_since_last_restart = current_time - last_restart_time
                min_restart_interval = 900  # 15 minutes minimum between restarts
                
                if restart_needed and time_since_last_restart < min_restart_interval:
                    minutes_to_wait = (min_restart_interval - time_since_last_restart) / 60
                    print(f"  - Device needs restart but was restarted {time_since_last_restart:.0f} seconds ago - waiting {minutes_to_wait:.1f} more minutes")
                    restart_needed = False
                
                # Handle restart if needed
                if restart_needed:
                    print(f"  - Restarting device - Reason: {restart_reason}")
                    success = await optimized_app_start(device_id, True)
                    
                    # Record restart time
                    device_status_cache[device_id]["last_restart_time"] = current_time
                    
                    if success:
                        print(f"  - Successfully restarted apps")
                        # Important: Update the status in the cache
                        device_status_cache[device_id]["is_alive"] = True
                        
                        # This is a system restart, not a status change from the API
                        # If it was offline before, we should send "back online" notification
                        if not was_alive:
                            print(f"  - Sending online notification after successful restart")
                            await notify_device_online(display_name, device_id)
                            status["last_online_notification"] = current_time
                            device_status_cache[device_id] = status
                    else:
                        print(f"  - Failed to restart apps")
                
                # Always update last status to track changes
                device_last_status[device_id] = {
                    "is_alive": is_alive
                }
                
            # Update UI with current status
            status_data = await get_status_data()
            await ws_manager.broadcast(status_data)
                
        except Exception as e:
            print(f"Error in API-based device monitoring: {str(e)}")
            traceback.print_exc()
        
        # Wait until next check
        await asyncio.sleep(monitoring_interval)

# Installation Functions
async def perform_installations(device_ips: List[str], extract_dir: Path):
    """
    Performs installations on multiple devices with progress tracking.
    Uses the optimized installation process.
    """
    global update_in_progress, current_progress
    
    try:
        update_in_progress = True
        total_devices = len(device_ips)
        
        device_increment = 100 / total_devices if total_devices > 0 else 100
        
        for index, ip in enumerate(device_ips, 1):
            try:
                start_progress = int((index - 1) * device_increment)
                end_progress = int(index * device_increment)
                
                update_progress(start_progress)
                print(f"Starting update for device {index}/{total_devices}: {ip}")
                
                # Run installation with progress tracking
                success = await optimized_perform_installation(ip, extract_dir)
                
                if success:
                    print(f"Successfully updated {ip}")
                else:
                    print(f"Failed to update {ip}")
                
                update_progress(end_progress)
                
            except Exception as e:
                print(f"Error updating {ip}: {str(e)}")
                update_progress(int(index * device_increment))
                clear_device_update_status(ip)
        
        update_progress(100)
        
        # Update UI with new status
        status_data = await get_status_data()
        await ws_manager.broadcast(status_data)
        
        await asyncio.sleep(2)
        
    finally:
        update_in_progress = False
        current_progress = 0

# API Status Update - Optimized to reduce ADB calls
async def update_api_status():
    """Periodically updates device status information from API with reduced ADB calls"""
    device_last_status = {}  # Track previous status for change detection
    
    while True:
        try:
            config = load_config()
            current_time = time.time()
            
            # Check if the required API configuration exists
            if not all(key in config for key in ["rotomApiUrl", "rotomApiUser", "rotomApiPass"]):
                print("API configuration incomplete, skipping check")
                await asyncio.sleep(60)
                continue
                
            async with httpx.AsyncClient() as client:
                auth = (config["rotomApiUser"], config["rotomApiPass"])
                response = await client.get(
                    config["rotomApiUrl"], 
                    auth=auth, 
                    timeout=10
                )
                
                # Check for successful response
                if response.status_code != 200:
                    print(f"API returned status code {response.status_code}")
                    await asyncio.sleep(60)
                    continue
                    
                try:
                    api_data = response.json()
                except json.JSONDecodeError:
                    print("Failed to parse API response as JSON")
                    await asyncio.sleep(60)
                    continue

            # Process each device
            for dev in config.get("devices", []):
                device_id = dev["ip"]  # This can be either IP:port or serial number
                
                # Determine if this is a USB device (no digits/periods/colons) or network device
                is_network_device = ":" in device_id and all(c.isdigit() or c == '.' or c == ':' for c in device_id)
                
                # Find matching device data, with more robust matching
                device_data = None
                details = get_device_details(device_id)
                display_name = details.get("display_name", "").lower()
                
                # For network devices, extract IP for matching
                device_ip_for_matching = None
                if is_network_device:
                    device_ip_for_matching = device_id.split(":")[0]
                
                for api_device in api_data.get("devices", []):
                    origin = api_device.get("origin", "").lower()
                    # Try different matching approaches
                    if (display_name and display_name in origin) or \
                       (device_ip_for_matching and device_ip_for_matching in origin):
                        device_data = api_device
                        break
                
                if not device_data:
                    device_data = {}
                
                # Get current status values from cache
                current_cache = device_status_cache.get(device_id, {})
                
                # Improved initialization of runtime tracking
                if device_id not in device_runtimes:
                    device_runtimes[device_id] = {
                        "start_time": current_time if current_cache.get("is_alive", False) else None,
                        "last_runtime": None
                    }
                    print(f"Initialized runtime tracking for {device_id}")
                
                # Add a variable to track when a device was first detected as offline
                first_detected_offline = current_cache.get("first_detected_offline", 0)
                
                # Handle memory values - keep old values if new ones are 0 or null
                current_mem_free = current_cache.get("mem_free", 0)
                new_mem_free = device_data.get("lastMemory", {}).get("memFree", 0)
                
                # If new memory value is 0 and current value is not 0, keep the current value
                if new_mem_free == 0 and current_mem_free > 0:
                    print(f"Ignoring zero memory value for {device_id}, keeping previous value: {current_mem_free}")
                    mem_free = current_mem_free
                else:
                    mem_free = new_mem_free
                
                # Handle isAlive status with improved grace period logic
                current_is_alive = current_cache.get("is_alive", False)
                new_is_alive = device_data.get("isAlive", False)
                
                # If device is newly detected as offline
                if current_is_alive and not new_is_alive:
                    # Store the timestamp of first offline detection
                    if first_detected_offline == 0:
                        first_detected_offline = current_time
                        print(f"Device {device_id} first detected offline at {datetime.datetime.fromtimestamp(current_time)}")
                # If device is online again, reset the offline detection timestamp
                elif new_is_alive:
                    first_detected_offline = 0
                
                # Check if the grace period is still active (60 seconds)
                grace_period = 60
                if (not new_is_alive and current_is_alive and first_detected_offline > 0 and 
                    (current_time - first_detected_offline < grace_period)):
                    print(f"Device {device_id} reported not alive but in grace period (since {int(current_time - first_detected_offline)} seconds)")
                    is_alive = True
                else:
                    # Outside grace period or never detected as offline
                    is_alive = new_is_alive
                    
                    # If a device is now officially marked as offline (after grace period)
                    if not is_alive and current_is_alive and first_detected_offline > 0:
                        print(f"Device {device_id} now officially offline after grace period expired ({int(current_time - first_detected_offline)} seconds)")
                
                # ADB connection is checked only when needed
                adb_status = True  # Assume connected unless proven otherwise
                adb_error = ""
                
                # Only check ADB connection if device is alive or for devices needing status check
                if is_alive or not current_cache.get("adb_status", False):
                    adb_status, adb_error = check_adb_connection(device_id)
                else:
                    # Reuse last status if device is offline
                    adb_status = current_cache.get("adb_status", False)
                    adb_error = current_cache.get("adb_error", "")
                
                # Check if device was offline and is now online (rebooted/restarted)
                prev_status = device_last_status.get(device_id, {})
                prev_is_alive = prev_status.get("is_alive", False)
                
                # Calculate current runtime
                current_runtime = None
                
                if is_alive and device_runtimes[device_id]["start_time"]:
                    current_runtime = current_time - device_runtimes[device_id]["start_time"]
                
                # Improved offline/online transition handling
                # If device just came back online - reset runtime counter
                if is_alive and not prev_is_alive:
                    print(f"Device {device_id} changed from offline to online, resetting runtime counter")
                    
                    # Don't overwrite existing last_runtime when coming back online
                    # Preserve the existing last_runtime value from the cache
                    existing_last_runtime = current_cache.get("last_runtime")
                    
                    # Only set a new runtime if there isn't already a valid one
                    if existing_last_runtime is None and current_cache.get("runtime") is not None and current_cache.get("runtime") > 60:
                        print(f"Storing previous runtime for {device_id}: {format_runtime(current_cache.get('runtime'))}")
                        device_runtimes[device_id]["last_runtime"] = current_cache.get("runtime")
                    elif existing_last_runtime is not None:
                        print(f"Preserving existing last_runtime for {device_id}: {format_runtime(existing_last_runtime)}")
                        device_runtimes[device_id]["last_runtime"] = existing_last_runtime
                    
                    # Set new start time
                    device_runtimes[device_id]["start_time"] = current_time
                    current_runtime = 0  # Just started
                    
                    # Force version refresh
                    version_manager.mark_for_refresh(device_id)
                
                # Handle online to offline transition as well
                elif not is_alive and prev_is_alive:
                    print(f"Device {device_id} changed from online to offline, preserving runtime")
                    # If we have a current runtime when going offline, store it
                    previous_runtime = current_cache.get("runtime", None)
                    if previous_runtime is not None and previous_runtime > 60:
                        print(f"Storing previous runtime for {device_id}: {format_runtime(previous_runtime)}")
                        device_runtimes[device_id]["last_runtime"] = previous_runtime
                        device_runtimes[device_id]["start_time"] = None
                
                # Update device status cache with all values
                device_status_cache[device_id] = {
                    "is_alive": is_alive,
                    "mem_free": mem_free,
                    "last_update": current_time,
                    "adb_status": adb_status,
                    "adb_error": adb_error,
                    "first_detected_offline": first_detected_offline,
                    "last_notification_time": current_cache.get("last_notification_time", 0),
                    "last_details_check": current_cache.get("last_details_check", 0),
                    "runtime": current_runtime if current_runtime and current_runtime > 0 else None,
                    "last_runtime": device_runtimes[device_id]["last_runtime"] if device_runtimes[device_id]["last_runtime"] and device_runtimes[device_id]["last_runtime"] > 60 else current_cache.get("last_runtime")
                }
                
                # Store current status for next comparison
                device_last_status[device_id] = {
                    "is_alive": is_alive
                }
                
                # Format runtime for display
                runtime_str = ""
                if current_runtime is not None and current_runtime > 0:
                    runtime_str = f" - Runtime: {format_runtime(current_runtime)}"
                    if device_runtimes[device_id]["last_runtime"] is not None and device_runtimes[device_id]["last_runtime"] > 60:
                        runtime_str += f" (last runtime: {format_runtime(device_runtimes[device_id]['last_runtime'])})"
                
                # Version info is only refreshed once every 5 minutes to reduce ADB calls
                if is_alive and adb_status and current_time - current_cache.get("last_details_check", 0) > 300:
                    # Only fetch on demand (triggered by state changes)
                    device_status_cache[device_id]["last_details_check"] = current_time

            # Send device status update to all WebSocket clients
            status_data = await get_status_data()
            await ws_manager.broadcast(status_data)

        except Exception as e:
            print(f"API Update Error: {str(e)}")
            import traceback
            traceback.print_exc()
        
        # Use the configured check interval or default to 15 seconds
        check_interval = config.get("api_check_interval", 15)
        await asyncio.sleep(check_interval)
        
# Helper Functions for Memory
def format_memory(value):
    """
    Converts memory values to readable formats
    Input value is in KB (not Bytes)!
    """
    try:
        if not value:
            return "N/A"
            
        size = float(value)
        
        if size < 1024:
            return f"{size:.1f} kB".replace(".", ",")
            
        size = size / 1024
        
        if size < 1024:
            return f"{size:.1f} MB".replace(".", ",")
            
        size = size / 1024
        return f"{size:.2f} GB".replace(".", ",")
    except:
        return "N/A"

def format_runtime(seconds):
    """Formats seconds to a readable format: Xh Ymin"""
    if seconds is None:
        return "unknown"
    
    hours = int(seconds // 3600)
    minutes = int((seconds % 3600) // 60)
    return f"{hours}h {minutes}m"

# WebSocket Status Data Function
async def get_status_data():
    """Collects status data for WebSocket updates, similar to /api/status endpoint"""
    config = load_config()
    devices = []
    
    versions = get_available_versions()
    pogo_latest = versions.get("latest", {}).get("version", "N/A")
    pogo_previous = versions.get("previous", {}).get("version", "N/A")

    current_time = time.time()
    last_version_debug = getattr(get_status_data, 'last_version_debug', 0)
    if not hasattr(get_status_data, 'last_versions') or get_status_data.last_versions != (pogo_latest, pogo_previous) or current_time - last_version_debug > 300:
        print(f"Status data - Latest: {pogo_latest}, Previous: {pogo_previous}")
        get_status_data.last_versions = (pogo_latest, pogo_previous)
        get_status_data.last_version_debug = current_time
    
    for dev in config["devices"]:
        ip = dev["ip"]
        status = device_status_cache.get(ip, {})
        details = get_device_details(ip)
        current_runtime = status.get("runtime")
        last_runtime = status.get("last_runtime")
        runtime_formatted = format_runtime(current_runtime) if current_runtime is not None else "N/A"
        last_runtime_formatted = format_runtime(last_runtime) if last_runtime is not None else "N/A"

        default_status = {
            "is_alive": False,
            "mem_free": 0,
            "last_update": 0,
            "adb_status": False,
            "adb_error": "No connection"
        }
        status = {**default_status, **status}
        
        # Check if device is in update process
        in_update = False
        update_info = ""
        if ip in devices_in_update and devices_in_update[ip]["in_update"]:
            in_update = True
            update_type = devices_in_update[ip]["update_type"]
            update_duration = int(time.time() - devices_in_update[ip]["started_at"])
            update_info = f"{update_type} ({update_duration}s)"
        
        devices.append({
            "display_name": details.get("display_name", ip.split(":")[0]),
            "ip": ip,
            "status": status.get("adb_status", False),
            "adb_error": status.get("adb_error", ""),
            "is_alive": status["is_alive"],
            "pogo": details.get("pogo_version", "N/A"),
            "mitm": details.get("mitm_version", "N/A"),
            "module": details.get("module_version", "N/A"),
            "mem_free": status.get("mem_free", 0),
            "last_update": status["last_update"],
            "control_enabled": dev.get("control_enabled", False),
            "in_update": in_update,
            "update_info": update_info,
            "runtime": current_runtime,
            "runtime_formatted": runtime_formatted,
            "last_runtime": last_runtime,
            "last_runtime_formatted": last_runtime_formatted
        })
    
    return {
        "devices": devices,
        "now": time.time(),
        "pogo_latest": pogo_latest,
        "pogo_previous": pogo_previous,
        "pif_auto_update_enabled": config.get("pif_auto_update_enabled", True),
        "pogo_auto_update_enabled": config.get("pogo_auto_update_enabled", True),
        "update_in_progress": update_in_progress,
        "update_progress": current_progress
    }

# Helper Functions
def update_progress(progress: int):
    """
    Updates the global progress indicator for UI updates
    
    Args:
        progress: Integer value between 0-100 representing progress percentage
    """
    global current_progress
    current_progress = progress

def is_logged_in(request: Request) -> bool:
    return request.session.get("logged_in", False)

def require_login(request: Request):
    if not is_logged_in(request):
        return RedirectResponse(url="/login", status_code=302)
    return None

def is_htmx_request(request: Request) -> bool:
    """Check if the request is coming from HTMX"""
    return request.headers.get("HX-Request") == "true"

def get_template_context(request: Request, **kwargs):
    """Get common template context with additional values"""
    context = {"request": request}
    context.update(kwargs)
    return context

async def get_status_data_with_tailwind_classes():
    """Enhanced version of get_status_data that adds Tailwind CSS-specific class information"""
    data = await get_status_data()
    
    for device in data["devices"]:
        device["adb_status_class"] = "text-green-500" if device["status"] else "text-red-500"
        device["alive_status_class"] = "text-green-500" if device["is_alive"] else "text-red-500"
        device["control_class"] = "bg-green-900/50 text-green-400" if device["control_enabled"] else "bg-gray-800 text-gray-400"
        
        # Add class for devices in update process
        if device.get("in_update", False):
            device["update_class"] = "bg-blue-900/30 text-blue-400 border-blue-700"
            device["status_badge"] = f"Updating: {device['update_info']}"
        elif not device["status"]:
            device["update_class"] = "bg-gray-800 text-gray-400"
            device["status_badge"] = "Offline"
        elif not device["is_alive"]:
            device["update_class"] = "bg-red-900/30 text-red-400 border-red-700"
            device["status_badge"] = "API Offline"
        else:
            device["update_class"] = "bg-green-900/30 text-green-400 border-green-700"
            device["status_badge"] = "Online"
    
    data["pif_auto_update_class"] = "bg-green-900/30 text-green-400 border-green-700" if data["pif_auto_update_enabled"] else "bg-red-900/30 text-red-400 border-red-700"
    data["pogo_auto_update_class"] = "bg-green-900/30 text-green-400 border-green-700" if data["pogo_auto_update_enabled"] else "bg-red-900/30 text-red-400 border-red-700"
    
    return data

# FastAPI Initialization
@asynccontextmanager
async def lifespan(app: FastAPI):
    # Initialize ADB connection pool
    adb_pool.cleanup_connections()
    
    # Sync ADB keys for authorization
    sync_system_adb_key()
    
    # Initialize with latest APK
    ensure_latest_apk_downloaded()
    
    # Start background tasks
    asyncio.create_task(update_api_status())
    asyncio.create_task(scheduled_update_task())
    asyncio.create_task(mapworld_update_task())
    
    # Start optimized background tasks
    asyncio.create_task(optimized_module_update_task())
    asyncio.create_task(optimized_pogo_update_task())
    asyncio.create_task(optimized_device_monitoring())
    yield

app = FastAPI(lifespan=lifespan)
app.add_middleware(SessionMiddleware, secret_key="CHANGE_ME_TO_A_SECURE_KEY")
app.mount("/static", StaticFiles(directory=str(BASE_DIR / "static")), name="static")
templates = Jinja2Templates(directory=str(BASE_DIR / "templates"))

# Add template filters and globals
templates.env.filters['format_memory'] = format_memory

templates.env.globals.update({
    'check_adb_connection': check_adb_connection,
    'get_device_display_name': lambda ip: get_device_details(ip)["display_name"],
    'get_available_versions': get_available_versions
})

# WebSocket Routes
@app.websocket("/ws/status")
async def websocket_endpoint(websocket: WebSocket):
    """WebSocket endpoint for real-time device status updates"""
    await ws_manager.connect(websocket)
    try:
        # Initial data
        status_data = await get_status_data()
        await websocket.send_json(status_data)
        
        # Keep connection alive
        while True:
            try:
                # Wait for client messages
                data = await websocket.receive_text()
                
                # Handle client commands
                if data == "refresh":
                    # Manual refresh requested
                    status_data = await get_status_data()
                    await websocket.send_json(status_data)
                elif data.startswith("refresh_device:"):
                    # Refresh specific device data
                    device_ip = data.split(":", 1)[1]
                    if device_ip:
                        # Force version refresh for this device
                        version_manager.mark_for_refresh(device_ip)
                        # Update status data
                        status_data = await get_status_data()
                        await websocket.send_json(status_data)
                
                # Wait a bit to avoid overloading
                await asyncio.sleep(0.1)
            except asyncio.TimeoutError:
                # Keep connection alive with ping-pong
                await asyncio.sleep(1)
    except WebSocketDisconnect:
        ws_manager.disconnect(websocket)
    except Exception as e:
        print(f"WebSocket error: {e}")
        ws_manager.disconnect(websocket)

# Regular Routes
@app.get("/", response_class=HTMLResponse)
def root(request: Request):
    if is_logged_in(request):
        return RedirectResponse(url="/status")
    return RedirectResponse(url="/login")

@app.get("/login", response_class=HTMLResponse)
def login_page(request: Request):
    return templates.TemplateResponse("login.html", {"request": request})

@app.post("/login", response_class=HTMLResponse)
def login_action(request: Request, username: str = Form(...), password: str = Form(...)):
    config = load_config()
    for user in config.get("users", []):
        if user["username"] == username and user["password"] == password:
            request.session["logged_in"] = True
            request.session["username"] = username
            
            # Add HX-Redirect header for HTMX requests
            response = RedirectResponse(url="/status", status_code=303)
            response.headers["HX-Redirect"] = "/status"
            return response
    
    # For HTMX requests, return a partial with error
    if is_htmx_request(request):
        error_message = """
        <div class="bg-red-900/50 border border-red-800 text-red-100 px-4 py-3 rounded mb-4" role="alert">
            <svg xmlns="http://www.w3.org/2000/svg" class="h-5 w-5 inline mr-1" fill="none" viewBox="0 0 24 24" stroke="currentColor">
                <path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M12 9v2m0 4h.01m-6.938 4h13.856c1.54 0 2.502-1.667 1.732-3L13.732 4c-.77-1.333-2.694-1.333-3.464 0L3.34 16c-.77 1.333.192 3 1.732 3z" />
            </svg>
            Invalid credentials
        </div>
        """
        return HTMLResponse(content=error_message)
    
    # Regular form submission
    return templates.TemplateResponse("login.html", {
        "request": request,
        "error": "Invalid credentials"
    })

@app.get("/logout")
def logout_action(request: Request):
    request.session.clear()
    return RedirectResponse(url="/login")

@app.get("/status", response_class=HTMLResponse)
def status_page(request: Request):
    if redirect := require_login(request):
        return redirect
    
    config = load_config()
    devices = []
    
    # Get PoGo version info for buttons
    versions = get_available_versions()
    pogo_latest = versions.get("latest", {}).get("version", "N/A")
    pogo_previous = versions.get("previous", {}).get("version", "N/A")
    
    for dev in config["devices"]:
        ip = dev["ip"]
        status = device_status_cache.get(ip, {})
        details = get_device_details(ip)
        
        default_status = {
            "is_alive": False,
            "mem_free": 0,
            "last_update": 0
        }
        status = {**default_status, **status}
        
        # Check if device is in update process
        in_update = False
        update_info = ""
        if ip in devices_in_update and devices_in_update[ip]["in_update"]:
            in_update = True
            update_type = devices_in_update[ip]["update_type"]
            update_duration = int(time.time() - devices_in_update[ip]["started_at"])
            update_info = f"{update_type} ({update_duration}s)"
        
        devices.append({
            "display_name": details.get("display_name", ip.split(":")[0]),
            "ip": ip,
            "status": check_adb_connection(ip)[0],
            "is_alive": "✅" if status["is_alive"] else "❌",
            "pogo": details.get("pogo_version", "N/A"),
            "mitm": details.get("mitm_version", "N/A"),
            "module": details.get("module_version", "N/A"),
            "mem_free": status.get("mem_free", 0),
            "last_update": status["last_update"],
            "control_enabled": dev.get("control_enabled", False),
            "in_update": in_update,
            "update_info": update_info
        })
    
    return templates.TemplateResponse("status.html", {
        "request": request,
        "username": request.session.get("username", ""),
        "devices": devices,
        "config": config,
        "now": time.time(),
        "pogo_latest": pogo_latest,
        "pogo_previous": pogo_previous
    })

@app.get("/settings", response_class=HTMLResponse)
def settings_page(request: Request):
    if redirect := require_login(request):
        return redirect
    return templates.TemplateResponse("settings.html", {
        "request": request,
        "config": load_config()
    })

@app.post("/settings/save", response_class=HTMLResponse)
def settings_save(
    request: Request,
    rotomApiUrl: str = Form(""),
    rotomApiUser: str = Form(""),
    rotomApiPass: str = Form(""),
    discord_webhook_url: str = Form("")
):
    if redirect := require_login(request):
        return redirect

    config = load_config()
    config.update({
        "rotomApiUrl": rotomApiUrl,
        "rotomApiUser": rotomApiUser,
        "rotomApiPass": rotomApiPass,
        "discord_webhook_url": discord_webhook_url
    })
    
    print(f"Saving settings with discord_webhook_url: {discord_webhook_url}")
    
    save_config(config)
    
    test_config = load_config()
    print(f"After save, discord_webhook_url is: {test_config.get('discord_webhook_url', 'NOT FOUND')}")
    
    return RedirectResponse(url="/settings", status_code=302)

@app.post("/devices/add", response_class=HTMLResponse)
def add_device(request: Request, new_ip: str = Form(...)):
    if redirect := require_login(request):
        return redirect
    
    device_id = format_device_id(new_ip.strip())
    print(f"Adding device with formatted ID: {device_id}")
    
    config = load_config()
    if not any(dev["ip"] == device_id for dev in config["devices"]):
        is_connected, error_msg = check_adb_connection(device_id)
        
        if ":" in device_id:
            display_name = device_id.split(":")[0]
        else:
            display_name = f"Device-{device_id[-4:]}" if len(device_id) > 4 else device_id
        
        config["devices"].append({
            "ip": device_id,
            "display_name": display_name,
            "control_enabled": False,
            "memory_threshold": 200,
            "pogo_version": "N/A",
            "mitm_version": "N/A",
            "module_version": "N/A"
        })
        save_config(config)
    
    return RedirectResponse(url="/settings", status_code=302)

@app.post("/devices/remove", response_class=HTMLResponse)
def remove_devices(request: Request, devices: List[str] = Form(...)):
    if redirect := require_login(request):
        return redirect
    
    config = load_config()
    config["devices"] = [dev for dev in config["devices"] if dev["ip"] not in devices]
    save_config(config)
    
    return RedirectResponse(url="/settings", status_code=302)

@app.post("/clear-cache")
def clear_cache(device_ip: Optional[str] = None):
    """Clear cache with optional device-specific targeting"""
    if device_ip:
        if ":" not in device_ip:
            device_ip = f"{device_ip}:5555"
            
        # Force version refresh
        version_manager.mark_for_refresh(device_ip)
        check_adb_connection.cache_clear()
        return {"status": f"Cache successfully cleared for {device_ip}"}
    else:
        # Clear all caches
        check_adb_connection.cache_clear()
        get_available_versions.cache_clear()
        return {"status": "Cache successfully cleared"}

@app.post("/devices/toggle-control", response_class=HTMLResponse)
def toggle_device_control(request: Request, device_ip: str = Form(...), control_enabled: Optional[str] = Form(None)):
    if redirect := require_login(request):
        return redirect
    
    config = load_config()
    for device in config["devices"]:
        if device["ip"] == device_ip:
            device["control_enabled"] = control_enabled is not None
            break
    
    save_config(config)
    return RedirectResponse(url="/settings", status_code=302)

@app.post("/devices/update-threshold", response_class=HTMLResponse)
def update_memory_threshold(request: Request, device_ip: str = Form(...), memory_threshold: int = Form(...)):
    if redirect := require_login(request):
        return redirect
    
    config = load_config()
    for device in config["devices"]:
        if device["ip"] == device_ip:
            device["memory_threshold"] = max(100, min(1000, memory_threshold))  # Constrain between 100-1000
            break
    
    save_config(config)
    return RedirectResponse(url="/settings", status_code=302)

@app.post("/pif/device-update", response_class=HTMLResponse)
async def pif_device_update(request: Request, device_ip: str = Form(...), version: str = Form(...), module_type: str = Form("fork")):
    global update_in_progress, current_progress

    device_id = format_device_id(device_ip)
    
    if redirect := require_login(request):
        return redirect
    
    try:
        update_in_progress = True
        update_progress(10)
        
        versions = await fetch_available_module_versions(module_type)
        update_progress(20)
        
        target_version = None
        for ver in versions:
            if ver["version"] == version and ver["module_type"] == module_type:
                target_version = ver
                break
        
        if not target_version:
            update_in_progress = False
            current_progress = 0
            return RedirectResponse(url=f"/status?error=Module version {version} not found", status_code=302)
        
        update_progress(30)
        
        update_progress(40)
        module_file = await download_module_version(target_version)
        update_progress(50)
        
        if not module_file:
            update_in_progress = False
            current_progress = 0
            return RedirectResponse(url=f"/status?error=Failed to download module version", status_code=302)
        
        update_progress(60)
        
        success = await install_module_with_progress(device_ip, module_file, module_type)
        
        if success:
            return RedirectResponse(url="/status?success=Module update completed", status_code=302)
        else:
            return RedirectResponse(url="/status?error=Module update failed", status_code=302)
            
    except Exception as e:
        print(f"Error updating device {device_ip} to module version {version}: {str(e)}")
        update_in_progress = False
        current_progress = 0
        return RedirectResponse(url="/status?error=Module update failed", status_code=302)

@app.post("/pogo/device-update", response_class=HTMLResponse)
async def pogo_device_update(request: Request, device_ip: str = Form(...), version: str = Form(...)):
    if redirect := require_login(request):
        return redirect

    device_id = format_device_id(device_ip)
    versions = get_available_versions()
    target_version = None
    
    for version_type in ["latest", "previous"]:
        if version_type in versions and versions[version_type].get("version") == version:
            target_version = versions[version_type]
    
    if not target_version:
        try:
            response = httpx.get(
                f"{POGO_MIRROR_URL}/index.json",
                timeout=10
            )
            if response.status_code == 200:
                all_versions = response.json()
                for entry in all_versions:
                    if entry["arch"] == DEFAULT_ARCH and entry["version"].replace(".apkm", "") == version:
                        target_version = {
                            "version": version,
                            "filename": f"com.nianticlabs.pokemongo_{DEFAULT_ARCH}_{version}.apkm",
                            "url": f"{POGO_MIRROR_URL}/apks/com.nianticlabs.pokemongo_{DEFAULT_ARCH}_{version}.apkm",
                            "arch": DEFAULT_ARCH
                        }
                        break
        except Exception as e:
            print(f"Error checking all versions: {str(e)}")
            return RedirectResponse(url="/status?error=Failed to check version", status_code=302)
    
    if not target_version:
        return RedirectResponse(url="/status?error=Version not found", status_code=302)
    
    try:
        apk_file = APK_DIR / target_version["filename"]
        if not apk_file.exists():
            apk_file = download_apk(target_version)
        
        specific_extract_dir = EXTRACT_DIR / target_version["version"]
        specific_extract_dir.mkdir(parents=True, exist_ok=True)
        unzip_apk(apk_file, specific_extract_dir)
        
        success = await optimized_perform_installation(device_ip, specific_extract_dir)
        
        if success:
            return RedirectResponse(url="/status?success=Pokemon GO updated successfully", status_code=302)
        else:
            return RedirectResponse(url="/status?error=Update failed", status_code=302)
    except Exception as e:
        print(f"Error updating device {device_ip} to version {version}: {str(e)}")
        return RedirectResponse(url="/status?error=Update failed", status_code=302)

@app.post("/pogo/update", response_class=HTMLResponse)
async def pogo_update(request: Request):
    if redirect := require_login(request):
        return redirect
    
    config = load_config()
    device_ips = [dev["ip"] for dev in config.get("devices", [])]
    
    versions = get_available_versions()
    if not versions:
        return RedirectResponse(url="/status?error=No versions found", status_code=302)
    
    entry = versions["latest"]
    apk_file = APK_DIR / entry["filename"]
    if not apk_file.exists():
        apk_file = download_apk(entry)
    
    version_extract_dir = EXTRACT_DIR / entry["version"]
    unzip_apk(apk_file, version_extract_dir)
    
    await perform_installations(device_ips, version_extract_dir)
    
    return RedirectResponse(url="/status", status_code=302)

@app.post("/settings/toggle-pif-autoupdate", response_class=HTMLResponse)
def toggle_pif_autoupdate(request: Request, enabled: Optional[str] = Form(None)):
    if redirect := require_login(request):
        return redirect
    
    config = load_config()
    config["pif_auto_update_enabled"] = enabled is not None
    save_config(config)
    
    return RedirectResponse(url="/settings", status_code=302)

@app.post("/settings/toggle-pogo-autoupdate", response_class=HTMLResponse)
def toggle_pogo_autoupdate(request: Request, enabled: Optional[str] = Form(None)):
    if redirect := require_login(request):
        return redirect
    
    config = load_config()
    config["pogo_auto_update_enabled"] = enabled is not None
    save_config(config)
    
    return RedirectResponse(url="/settings", status_code=302)

@app.get("/update-status")
def get_update_status():
    return {
        "status": update_in_progress,
        "progress": current_progress,
        "message": "Installation in progress..." if update_in_progress else "Idle"
    }

@app.get("/api/status")
async def api_status(request: Request):
    if not is_logged_in(request):
        return {"error": "Not authenticated"}
    
    status_data = await get_status_data_with_tailwind_classes()
    return status_data

@app.get("/api/pif-versions")
async def api_pif_versions(request: Request):
    """Endpoint to get available PIF versions"""
    if not is_logged_in(request):
        return {"error": "Not authenticated"}
        
    versions = await get_pif_versions_for_ui()
    return {"versions": versions}

@app.get("/api/all-module-versions")
async def api_all_module_versions(request: Request):
    """Returns combined module versions for UI"""
    if not is_logged_in(request):
        return {"error": "Not authenticated"}
        
    versions = await get_all_module_versions_for_ui()
    return versions

@app.post("/settings/set-module-preference")
async def set_module_preference(request: Request, module_type: str = Form(...)):
    """Sets the preferred module type in configuration"""
    if not is_logged_in(request):
        return RedirectResponse(url="/login", status_code=302)
    
    if module_type not in ["fork", "fix"]:
        module_type = "fork"
    
    config = save_module_preference(module_type)
    
    return RedirectResponse(url="/settings?success=Module preference updated successfully", status_code=302)

@app.post("/devices/restart-apps", response_class=HTMLResponse)
async def restart_apps(request: Request, device_ip: str = Form(...)):
    if redirect := require_login(request):
        return redirect
    
    try:
        device_id = format_device_id(device_ip)
        
        device_details = get_device_details(device_id)
        display_name = device_details.get("display_name", device_id.split(":")[0] if ":" in device_id else device_id)
        
        config = load_config()
        device = next((d for d in config["devices"] if d["ip"] == device_id), None)
        control_enabled = device and device.get("control_enabled", False)
        
        print(f"Restarting apps on {device_id}...")
        success = await optimized_app_start(device_id, control_enabled)
        
        if success:
            return RedirectResponse(url="/status?success=Apps restarted successfully", status_code=302)
        else:
            return RedirectResponse(url="/status?error=Failed to restart apps", status_code=302)
    except Exception as e:
        print(f"Error restarting apps on {device_id}: {str(e)}")
        return RedirectResponse(url="/status?error=Failed to restart apps", status_code=302)

@app.post("/devices/reboot", response_class=HTMLResponse)
def reboot_device(request: Request, device_ip: str = Form(...)):
    if redirect := require_login(request):
        return redirect
    
    try:
        device_id = format_device_ip = format_device_id(device_ip)
        
        device_details = get_device_details(device_id)
        display_name = device_details.get("display_name", device_id.split(":")[0] if ":" in device_id else device_id)
        
        print(f"Rebooting device {device_id}...")
        
        adb_pool.execute_command(device_id, ["adb", "reboot"])
        
        return RedirectResponse(url="/status?success=Reboot command sent", status_code=302)
    except Exception as e:
        print(f"Error rebooting device {device_id}: {str(e)}")
        return RedirectResponse(url="/status?error=Failed to reboot device", status_code=302)

@app.post("/devices/authorize", response_class=HTMLResponse)
def authorize_device(request: Request, device_ip: str = Form(...)):
    if redirect := require_login(request):
        return redirect
    
    try:
        device_id = format_device_id(device_ip)
        
        success = streamlined_adb_authorization(device_id)
        
        if success:
            return RedirectResponse(url="/settings?success=Device authorized successfully", status_code=302)
        else:
            return RedirectResponse(url="/settings?error=Failed to authorize device. Root access required.", status_code=302)
    except Exception as e:
        print(f"Error authorizing device {device_ip}: {str(e)}")
        return RedirectResponse(url="/settings?error=Authorization error: {str(e)}", status_code=302)

@app.websocket("/ws/htmx/status")
async def websocket_htmx_endpoint(websocket: WebSocket):
    """WebSocket endpoint for HTMX streaming updates"""
    await ws_manager.connect(websocket)
    try:
        status_data = await get_status_data()
        html_response = templates.TemplateResponse(
            "partials/device_table.html", 
            {"request": {}, "devices": status_data["devices"]}
        )
        await websocket.send_text(html_response.body.decode())
        
        while True:
            try:
                data = await websocket.receive_text()
                
                if data == "refresh":
                    status_data = await get_status_data()
                    html_response = templates.TemplateResponse(
                        "partials/device_table.html", 
                        {"request": {}, "devices": status_data["devices"]}
                    )
                    await websocket.send_text(html_response.body.decode())
            except asyncio.TimeoutError:
                await asyncio.sleep(1)
    except WebSocketDisconnect:
        ws_manager.disconnect(websocket)

@app.get("/api/update-progress", response_class=HTMLResponse)
def get_update_progress():
    """Returns the current update progress as HTML for HTMX"""
    progress_html = f"""
    <div class="bg-dark-800 rounded-lg p-4 border border-gray-700">
        <div class="overflow-hidden h-2 mb-4 text-xs flex rounded bg-gray-700">
            <div class="w-{current_progress}% shadow-none flex flex-col text-center whitespace-nowrap text-white justify-center bg-blue-500 transition-all duration-500"></div>
        </div>
        <p class="text-center text-sm text-gray-300">
            {current_progress}% Complete
        </p>
    </div>
    """
    return HTMLResponse(content=progress_html)

if __name__ == "__main__":
    import uvicorn
    uvicorn.run(app, host="0.0.0.0", port=8000)