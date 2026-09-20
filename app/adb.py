"""ADB device connectivity (connection pool, keys, checks)"""
import os
import platform
import subprocess
import threading
import time
import traceback

from .config import BASE_DIR, TimeoutConfig
from .utils import format_device_id, log, ttl_cache

class ADBConnectionPool:
    """
    Manages ADB connections to devices and minimizes
    reconnection attempts by tracking connection status.
    """
    def __init__(self):
        self.connected_devices = set()
        self.last_command_time = {}  # Track when last command was sent to each device
        self.device_status_cache = {}
        self.update_lock = threading.Lock()
        self.config_lock = threading.RLock()
        self.update_in_progress = False
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
                    log("Newly connected via ADB", device_id, "INFO")
                
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
            log(f"Batch command failed: {result.stderr}", device_id, "ERROR")
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
adb_pool = ADBConnectionPool()
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

            # Check if device is unauthorized (needs user confirmation on device)
            try:
                devices_result = subprocess.run(
                    ["adb", "devices"],
                    capture_output=True, text=True,
                    timeout=5
                )
                if f"{device_id}\tunauthorized" in devices_result.stdout:
                    return False, "Device unauthorized: Please confirm ADB authorization on the device"
            except Exception:
                pass

            # For network devices, try explicit reconnection
            if is_network_device:
                try:
                    # Disconnect first to reset connection state
                    subprocess.run(
                        ["adb", "disconnect", device_id],
                        capture_output=True, text=True,
                        timeout=10
                    )
                    time.sleep(0.5)  # Brief pause for cleanup

                    # Reconnect
                    connect_result = subprocess.run(
                        ["adb", "connect", device_id],
                        capture_output=True, text=True,
                        timeout=15
                    )

                    # Check for specific error patterns
                    stdout = connect_result.stdout.lower()
                    if "failed to authenticate" in stdout:
                        return False, "Authentication error: Device not authorized"
                    elif "already connected" in stdout or "connected to" in stdout:
                        # Verify the connection worked
                        if adb_pool.ensure_connected(device_id):
                            return True, ""
                        # Check if device is unauthorized after connect
                        try:
                            devices_result = subprocess.run(
                                ["adb", "devices"],
                                capture_output=True, text=True,
                                timeout=5
                            )
                            if f"{device_id}\tunauthorized" in devices_result.stdout:
                                return False, "Device unauthorized: Please confirm ADB authorization on the device"
                        except Exception:
                            pass
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
            log(f"Creating Android directory: {android_dir}", None, "CONFIG")
            os.makedirs(android_dir, exist_ok=True)
        
        private_key_exists = os.path.exists(adb_private_key) and os.path.getsize(adb_private_key) > 0
        
        public_key_exists = os.path.exists(adb_public_key) and os.path.getsize(adb_public_key) > 0
        
        if not private_key_exists:
            log("Private ADB key not found, generating new keys", None, "CONFIG")
            try:
                subprocess.run(["adb", "keygen", adb_private_key], check=True, timeout=TimeoutConfig.ADB_KEYGEN)
                private_key_exists = os.path.exists(adb_private_key) and os.path.getsize(adb_private_key) > 0
                log(f"Generated private key with adb keygen: {private_key_exists}", None, "CONFIG")
            except (subprocess.SubprocessError, FileNotFoundError) as e:
                log(f"adb keygen failed: {str(e)}, trying alternative approach", None, "CONFIG")
                
                try:
                    subprocess.run(
                        ["openssl", "genrsa", "-out", adb_private_key, "2048"],
                        check=True, timeout=10
                    )
                    private_key_exists = os.path.exists(adb_private_key) and os.path.getsize(adb_private_key) > 0
                    log(f"Generated private key with OpenSSL: {private_key_exists}", None, "CONFIG")
                except (subprocess.SubprocessError, FileNotFoundError) as e:
                    log(f"Failed to generate private key with OpenSSL: {str(e)}", None, "ERROR")
        
        if private_key_exists and not public_key_exists:
            log("Public key not found, generating from private key", None, "CONFIG")
            try:
                subprocess.run(
                    ["openssl", "rsa", "-in", adb_private_key, "-pubout", "-out", adb_public_key],
                    check=True, timeout=10
                )
                public_key_exists = os.path.exists(adb_public_key) and os.path.getsize(adb_public_key) > 0
                log(f"Generated public key: {public_key_exists}", None, "CONFIG")
            except (subprocess.SubprocessError, FileNotFoundError) as e:
                log(f"Failed to generate public key: {str(e)}", None, "ERROR")
        
        if public_key_exists:
            with open(adb_public_key, "r", encoding="utf-8") as f:
                content = f.read().strip()
                log(f"Found ADB public key ({len(content)} bytes)", None, "CONFIG")
                return content
        else:
            log("Failed to ensure ADB keys exist", None, "ERROR")
            return ""
    except Exception as e:
        log(f"Error ensuring ADB keys: {str(e)}", None, "ERROR")
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
            log(f"System ADB key not found at {system_key_path}", None, "CONFIG")
            return False
        
        if not additional_keys_dir.exists():
            log(f"Creating additional keys directory: {additional_keys_dir}", None, "CONFIG")
            additional_keys_dir.mkdir(parents=True, exist_ok=True)
        
        with open(system_key_path, "r", encoding="utf-8") as f:
            key_content = f.read().strip()
            
        if not key_content:
            log("System ADB key is empty, nothing to sync", None, "CONFIG")
            return False
            
        with open(target_key_path, "w", encoding="utf-8") as f:
            f.write(key_content)
            
        log(f"Synchronized system ADB key to {target_key_path}", None, "CONFIG")
        return True
            
    except Exception as e:
        log(f"Error synchronizing system ADB key: {str(e)}", None, "ERROR")
        return False
