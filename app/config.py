"""Config persistence, load/save, defaults, constants"""
from pathlib import Path
import json
import os
import shutil
import tempfile
import threading

from .utils import clear_display_name_cache, log

BASE_DIR = Path(__file__).resolve().parent.parent
CONFIG_FILE = BASE_DIR / "config.json"
APK_DIR = BASE_DIR / "data" / "apks" / "pogo"  # Google/APKM
S_APK_DIR = BASE_DIR / "data" / "apks" / "s-pogo"  # Samsung/APK
EXTRACT_DIR = APK_DIR / "extracted"
POGO_MIRROR_URL = "https://mirror.unownhash.com"
DEFAULT_ARCH = "arm64-v8a"
config_lock = threading.RLock()
def save_config(config):
    """
    Saves the configuration to config.json.
    Creates a backup before writing. Uses atomic write (temp file + rename)
    to prevent data loss on crash.
    """
    with config_lock:
        try:
            # Create backup if config file exists
            if CONFIG_FILE.exists():
                backup_file = CONFIG_FILE.with_suffix('.json.bak')
                try:
                    shutil.copy2(CONFIG_FILE, backup_file)
                except Exception as e:
                    log(f"Warning: Could not create config backup: {e}", None, "CONFIG")

            # Atomic write: write to temp file first, then rename
            config_dir = CONFIG_FILE.parent
            tmp_fd, tmp_path = tempfile.mkstemp(dir=str(config_dir), suffix='.json.tmp')
            try:
                with os.fdopen(tmp_fd, "w", encoding="utf-8") as f:
                    json.dump(config, f, indent=4, ensure_ascii=False)
                    f.flush()
                    os.fsync(f.fileno())
                try:
                    os.replace(tmp_path, str(CONFIG_FILE))
                except OSError:
                    # Fallback for Docker bind-mounts or locked files
                    # where os.replace() fails with "Device or resource busy"
                    shutil.copy2(tmp_path, str(CONFIG_FILE))
                    os.unlink(tmp_path)
            except Exception:
                if os.path.exists(tmp_path):
                    os.unlink(tmp_path)
                raise

            # Clear display name cache when config changes
            clear_display_name_cache()

        except Exception as e:
            log(f"Error saving config: {e}", None, "ERROR")
            # Try to restore from backup
            backup_file = CONFIG_FILE.with_suffix('.json.bak')
            if backup_file.exists():
                log("Attempting to restore config from backup", None, "CONFIG")
                try:
                    shutil.copy2(backup_file, CONFIG_FILE)
                    log("Config restored from backup", None, "CONFIG")
                except Exception as restore_error:
                    log(f"Failed to restore config: {restore_error}", None, "ERROR")
def load_config():
    """
    Loads the configuration from config.json.
    If the file doesn't exist, creates it with default values.
    On read errors, attempts to load from backup before falling back to defaults.
    """
    default_config = {
        "devices": [],
        "users": [],
        "discord_webhook_url": "",
        "pif_auto_update_enabled": True,
        "pogo_auto_update_enabled": True,
        "pif_module_sources": [
            {
                "name": "PlayIntegrityFork (Official)",
                "repo": "osm0sis/PlayIntegrityFork",
                "enabled": True,
                "is_default": True
            }
        ],
        "pogo_sources": [
            {
                "name": "UnownHash Mirror",
                "type": "mirror",
                "url": POGO_MIRROR_URL,
                "enabled": True,
                "is_default": True
            }
        ]
    }

    with config_lock:
        if not CONFIG_FILE.exists():
            log(f"Config file not found, creating default config", None, "CONFIG")
            save_config(default_config)
            return default_config

        try:
            with open(CONFIG_FILE, "r", encoding="utf-8") as f:
                config = json.load(f)
        except (json.JSONDecodeError, IOError) as e:
            log(f"Error reading config file: {e}", None, "ERROR")
            # Try backup before falling back to defaults
            backup_file = CONFIG_FILE.with_suffix('.json.bak')
            if backup_file.exists():
                try:
                    log("Attempting to load config from backup", None, "CONFIG")
                    with open(backup_file, "r", encoding="utf-8") as f:
                        config = json.load(f)
                    log("Config loaded from backup successfully", None, "CONFIG")
                    save_config(config)  # Restore backup as active config
                except (json.JSONDecodeError, IOError) as backup_error:
                    log(f"Backup also corrupted: {backup_error}, creating default config", None, "ERROR")
                    save_config(default_config)
                    return default_config
            else:
                log("No backup available, creating default config", None, "ERROR")
                save_config(default_config)
                return default_config

        # Ensure all required fields exist
        for device in config.get("devices", []):
            device.setdefault("display_name", device["ip"].split(":")[0])
            device.setdefault("pogo_version", "N/A")
            device.setdefault("mitm_version", "N/A")
            device.setdefault("module_version", "N/A")
            device.setdefault("control_enabled", False)
            device.setdefault("memory_threshold", 200)
        config.setdefault("devices", [])
        config.setdefault("users", [])
        config.setdefault("discord_webhook_url", "")
        config.setdefault("pif_auto_update_enabled", True)
        config.setdefault("pogo_auto_update_enabled", True)
        config.setdefault("device_token", "")
        config.setdefault("discord_bot_token", "")
        config.setdefault("discord_bot_channel_id", "")
        config.setdefault("discord_bot_role_id", "")
        config.setdefault("discord_bot_notify_channel_id", "")
        config.setdefault("pif_module_sources", [
            {
                "name": "PlayIntegrityFork (Official)",
                "repo": "osm0sis/PlayIntegrityFork",
                "enabled": True,
                "is_default": True
            }
        ])
        config.setdefault("pogo_sources", [
            {
                "name": "UnownHash Mirror",
                "type": "mirror",
                "url": POGO_MIRROR_URL,
                "enabled": True,
                "is_default": True
            }
        ])
        return config
def needs_setup() -> bool:
    """Check if initial setup is needed (no users configured)."""
    config = load_config()
    return len(config.get("users", [])) == 0
def update_device_info(ip: str, details: dict, furtif_config: dict = None):
    """
    Updates device information in config.json.
    
    Args:
        ip: Device IP address
        details: Device details (display_name, versions)
        furtif_config: Optional Furtif/Map World config settings
    """
    config = load_config()
    for device in config["devices"]:
        if device["ip"] == ip:
            device.update({
                "display_name": details["display_name"],
                "pogo_version": details.get("pogo_version", "N/A"),
                "mitm_version": details.get("mitm_version", "N/A"),
                "module_version": details.get("module_version", "N/A")
            })
            # Save Furtif config if provided
            if furtif_config:
                device["furtif_config"] = furtif_config
    save_config(config)
class TimeoutConfig:
    SHORT = 5      # Quick operations (disconnect, simple checks)  
    MEDIUM = 10    # Standard operations (connect, version checks)
    LONG = 30      # Complex operations (installations, downloads)
    HTTP = 15      # HTTP requests
    ADB_KEYGEN = 10 # ADB key generation
