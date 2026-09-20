"""Per-device config, tokens and details"""
from typing import Dict, Tuple
import asyncio
import base64
import httpx
import json
import os
import re
import subprocess
import tempfile
import time

from .config import load_config, save_config, update_device_info
from .discord_bot import notify_invalid_token
from .utils import format_device_id, log

_token_validation_cache: Dict[str, Tuple[bool, str, float]] = {}
TOKEN_CACHE_TTL = 300  # 5 minutes
async def validate_device_token(token: str, bypass_cache: bool = False) -> Tuple[bool, str]:
    """
    Validates a device token against the Protomines API.
    Results are cached for 5 minutes to reduce API calls.
    Retries up to 3 times on server errors (HTTP 5xx).

    Args:
        token: The encoded token to validate
        bypass_cache: If True, skip the cache and force a fresh API call

    Returns:
        Tuple[bool, str]: (is_valid, message)
        - is_valid: True if token is valid and has access
        - message: API response message
    """
    if not token or not token.strip():
        return (False, "No token provided")

    token_stripped = token.strip()

    # Check cache first (unless bypassed)
    if not bypass_cache and token_stripped in _token_validation_cache:
        cached_valid, cached_msg, cached_time = _token_validation_cache[token_stripped]
        if time.time() - cached_time < TOKEN_CACHE_TTL:
            log(f"Token validation from cache: valid={cached_valid}", None, "CONFIG")
            return (cached_valid, cached_msg)

    # Fixed internal validation URL
    validation_url = "https://protomines.ddns.net/api/access/get_access_status.php"

    max_retries = 3
    for attempt in range(max_retries):
        try:
            async with httpx.AsyncClient() as client:
                response = await client.post(
                    validation_url,
                    json={"encoded_token": token_stripped},
                    headers={"Content-Type": "application/json"},
                    timeout=15
                )

                if response.status_code >= 500 and attempt < max_retries - 1:
                    wait_time = 2 ** attempt  # 1s, 2s
                    log(f"Token validation API returned {response.status_code}, retrying in {wait_time}s (attempt {attempt + 1}/{max_retries})", None, "WARN")
                    await asyncio.sleep(wait_time)
                    continue

                if response.status_code != 200:
                    log(f"Token validation API returned status {response.status_code}", None, "ERROR")
                    return (False, f"API error: HTTP {response.status_code}")

                result = response.json()

                success = result.get("success", False)
                message = result.get("message", "Unknown response")
                # Optional: If the API returns specific access levels or device tokens, they can be handled here (added in 3.00+)
                device_token = result.get("device_token", None)

                # If a device_token was returned from the API, save it to config
                if device_token:
                    try:
                        config = load_config()
                        if config.get("device_token") != device_token:
                            config["device_token"] = device_token
                            save_config(config)
                            log("Device token updated from API response", None, "CONFIG")
                    except Exception as e:
                        log(f"Failed to save device token from API: {e}", None, "ERROR")

                # Cache the result
                _token_validation_cache[token_stripped] = (success, message, time.time())

                if success:
                    log(f"Token validated successfully: {message}", None, "CONFIG")
                    return (True, message)
                else:
                    log(f"Token validation failed: {message}", None, "CONFIG")
                    return (False, message)

        except httpx.TimeoutException:
            if attempt < max_retries - 1:
                wait_time = 2 ** attempt
                log(f"Token validation timed out, retrying in {wait_time}s (attempt {attempt + 1}/{max_retries})", None, "WARN")
                await asyncio.sleep(wait_time)
                continue
            log("Token validation timed out after all retries", None, "ERROR")
            return (False, "Validation timeout")
        except json.JSONDecodeError:
            log("Token validation returned invalid JSON", None, "ERROR")
            return (False, "Invalid API response")
        except Exception as e:
            if attempt < max_retries - 1:
                wait_time = 2 ** attempt
                log(f"Token validation error: {str(e)}, retrying in {wait_time}s (attempt {attempt + 1}/{max_retries})", None, "WARN")
                await asyncio.sleep(wait_time)
                continue
            log(f"Token validation error: {str(e)}", None, "ERROR")
            return (False, f"Validation error: {str(e)}")

    return (False, "Validation failed after all retries")
def get_device_package_name(device_id: str) -> str:
    """
    Gets the Pokemon GO package name for the device from its Furtif config.
    Falls back to default if config is not available.
    
    Args:
        device_id: Device identifier
        
    Returns:
        str: The package name (either com.nianticlabs.pokemongo or com.nianticlabs.pokemongo.ares)
    """
    try:
        furtif_config = read_device_furtif_config(device_id)
        pkg = furtif_config.get("PackageName", "com.nianticlabs.pokemongo")
        
        # Validate package name is one of the supported options
        if pkg in ("com.nianticlabs.pokemongo", "com.nianticlabs.pokemongo.ares"):
            return pkg
        else:
            return "com.nianticlabs.pokemongo"
    except Exception as e:
        log(f"Error getting device package name, using default: {str(e)}", device_id, "CONFIG")
        return "com.nianticlabs.pokemongo"
def read_device_furtif_config(device_id: str) -> dict:
    """
    Reads the Furtif/Map World config from the device and extracts
    all relevant settings. Prefers JSON parsing; falls back to regex
    for non-JSON formats (works with both JSON and JS object format).

    Args:
        device_id: Device identifier

    Returns:
        dict: Dictionary containing the extracted config settings, empty dict on error
    """
    device_id = format_device_id(device_id)
    furtif_config = {}

    try:
        cmd = f'adb -s {device_id} shell "su -c \'base64 /data/data/com.github.furtif.furtifformaps/files/config.json\'"'
        result = subprocess.run(cmd, shell=True, capture_output=True, text=True, timeout=10)

        if not (result.returncode == 0 and result.stdout):
            log(f"Could not read Furtif config.json (returncode={result.returncode})", device_id, "CONFIG")
            return furtif_config

        try:
            raw_output = base64.b64decode(result.stdout.strip()).decode('utf-8').strip()
        except Exception as decode_err:
            log(f"Base64 decode failed, falling back to raw output: {decode_err}", device_id, "CONFIG")
            raw_output = result.stdout.strip()

        # --- Attempt 1: parse as valid JSON ---
        json_start = raw_output.find('{')
        json_end = raw_output.rfind('}')
        parsed = None
        if json_start != -1 and json_end != -1:
            try:
                parsed = json.loads(raw_output[json_start:json_end + 1])
            except json.JSONDecodeError:
                pass

        if parsed is not None:
            # Boolean fields
            for bool_key, default in [
                ("IsRotomMode", False),
                ("RotomRpcJailMode", False),
                ("RotomTryAutoStart", False),
                ("RotomCheckPgoForced", False),
                ("RotomUsesCmds", False),
                ("RotomIgnoreUnity", False),
                ("RotomIgnoreDelays", False),
                ("RotomUseRealPublicIp", False),
            ]:
                furtif_config[bool_key] = bool(parsed.get(bool_key, default))

            # Integer fields
            for int_key, default in [("RotomDelayLoader", 3), ("RotomMaxWorkers", 60)]:
                try:
                    furtif_config[int_key] = int(parsed.get(int_key, default))
                except (TypeError, ValueError):
                    furtif_config[int_key] = default

            # String fields
            furtif_config["DiscordData"] = str(parsed.get("DiscordData", ""))
            furtif_config["RotomSecret"] = str(parsed.get("RotomSecret", ""))
            furtif_config["RotomURL"] = str(parsed.get("RotomURL", ""))
            furtif_config["RotomDeviceName"] = str(parsed.get("RotomDeviceName", ""))
            pkg = str(parsed.get("PackageName", "com.nianticlabs.pokemongo"))
            furtif_config["PackageName"] = pkg if pkg in (
                "com.nianticlabs.pokemongo", "com.nianticlabs.pokemongo.ares"
            ) else "com.nianticlabs.pokemongo"

        else:
            # --- Attempt 2: regex fallback for non-JSON formats ---
            def _bool(key, default=False):
                m = re.search(rf'{key}["\s]*:["\s]*(true|false)', raw_output, re.IGNORECASE)
                return m.group(1).lower() == "true" if m else default

            def _str_quoted(key, default=""):
                m = re.search(rf'{key}["\s]*:\s*"([^"]*)"', raw_output)
                return m.group(1) if m else default

            def _str_bare(key, default=""):
                m = re.search(rf'{key}["\s]*:["\s]*([^,}}\s]+)', raw_output)
                return m.group(1).strip().strip('"') if m else default

            def _int(key, default):
                m = re.search(rf'{key}["\s]*:["\s]*(\d+)', raw_output)
                return int(m.group(1)) if m else default

            furtif_config["IsRotomMode"] = _bool("IsRotomMode")
            furtif_config["RotomRpcJailMode"] = _bool("RotomRpcJailMode")
            furtif_config["RotomTryAutoStart"] = _bool("RotomTryAutoStart")
            furtif_config["RotomCheckPgoForced"] = _bool("RotomCheckPgoForced")
            furtif_config["RotomUsesCmds"] = _bool("RotomUsesCmds")
            furtif_config["RotomIgnoreUnity"] = _bool("RotomIgnoreUnity")
            furtif_config["RotomIgnoreDelays"] = _bool("RotomIgnoreDelays")
            furtif_config["RotomUseRealPublicIp"] = _bool("RotomUseRealPublicIp")
            furtif_config["RotomDelayLoader"] = _int("RotomDelayLoader", 3)
            furtif_config["RotomMaxWorkers"] = _int("RotomMaxWorkers", 60)
            furtif_config["DiscordData"] = _str_bare("DiscordData", "")
            furtif_config["RotomSecret"] = _str_quoted("RotomSecret", "")
            furtif_config["RotomURL"] = _str_quoted("RotomURL", "")
            furtif_config["RotomDeviceName"] = _str_bare("RotomDeviceName", "")
            pkg = _str_bare("PackageName", "com.nianticlabs.pokemongo")
            furtif_config["PackageName"] = pkg if pkg in (
                "com.nianticlabs.pokemongo", "com.nianticlabs.pokemongo.ares"
            ) else "com.nianticlabs.pokemongo"

        log(
            f"Furtif config read: RotomURL={furtif_config.get('RotomURL')!r}, "
            f"RotomDelayLoader={furtif_config.get('RotomDelayLoader')}, "
            f"DiscordData={'present' if furtif_config.get('DiscordData') else 'empty'}",
            device_id, "CONFIG"
        )

    except subprocess.TimeoutExpired:
        log("Timeout reading Furtif config.json", device_id, "ERROR")
    except Exception as e:
        log(f"Error reading Furtif config: {e}", device_id, "ERROR")

    return furtif_config
def write_device_discord_token(device_id: str, token: str) -> Tuple[bool, str]:
    """
    Writes the DiscordData token to the MapWorld config on the device.
    ONLY works with valid JSON config files.
    If the config is invalid JSON, it will be DELETED so MapWorld creates a fresh one.
    
    Args:
        device_id: Device identifier
        token: The token to write (with normal '=' characters)
        
    Returns:
        Tuple[bool, str]: (success, error_message)
        Special error: "INVALID_CONFIG_DELETED" means the config was deleted and needs recreation
    """
    device_id = format_device_id(device_id)
    config_path = "/data/data/com.github.furtif.furtifformaps/files/config.json"
    
    try:
        # First, read the current config from device (using base64 to preserve special chars)
        read_cmd = f'adb -s {device_id} shell "su -c \'base64 {config_path}\'"'
        result = subprocess.run(read_cmd, shell=True, capture_output=True, text=True, timeout=10)

        if result.returncode != 0 or not result.stdout:
            return False, f"Could not read config from device: {result.stderr}"

        try:
            raw_output = base64.b64decode(result.stdout.strip()).decode('utf-8').strip()
        except Exception as decode_err:
            log(f"Base64 decode failed, falling back to raw output: {decode_err}", device_id, "CONFIG")
            raw_output = result.stdout.strip()
        
        # Check if config has content
        if not raw_output or '{' not in raw_output:
            return False, "Config file is empty or invalid"
        
        # Find JSON boundaries
        json_start = raw_output.find('{')
        json_end = raw_output.rfind('}')
        
        if json_start == -1 or json_end == -1:
            return False, "Could not find JSON boundaries in config"
        
        config_content = raw_output[json_start:json_end + 1]
        
        # Try to parse as JSON - ONLY accept valid JSON, no fixing attempts
        device_config = None
        try:
            device_config = json.loads(config_content)
            log("Config parsed as valid JSON", device_id, "CONFIG")
        except json.JSONDecodeError as e:
            log(f"Config is NOT valid JSON: {e}", device_id, "ERROR")
            log("DELETING invalid config - MapWorld must create a new one", device_id, "CONFIG")
            
            # Delete the invalid config file
            delete_cmd = f'adb -s {device_id} shell "su -c \'rm -f {config_path}\'"'
            delete_result = subprocess.run(delete_cmd, shell=True, capture_output=True, text=True, timeout=10)
            
            if delete_result.returncode == 0:
                log("Invalid config file deleted successfully", device_id, "CONFIG")
                return False, "INVALID_CONFIG_DELETED"
            else:
                return False, f"Config is invalid JSON and could not be deleted: {delete_result.stderr}"
        
        # At this point we have a valid device_config dict
        # Update the DiscordData field
        device_config["DiscordData"] = token
        
        # Convert back to JSON (ensure_ascii=True converts = to \u003d)
        new_content = json.dumps(device_config, ensure_ascii=True)
        
        # Double-check the output is valid JSON before writing
        try:
            verify = json.loads(new_content)
            if "DiscordData" not in verify:
                return False, "Safety check failed: DiscordData missing from output"
            log(f"Output verified: valid JSON with {len(verify)} keys", device_id, "CONFIG")
        except json.JSONDecodeError as e:
            return False, f"Safety check failed: Output is not valid JSON: {e}"
        
        # Write the new config to a temp file locally, then push to device
        temp_local = tempfile.NamedTemporaryFile(mode='w', suffix='.json', delete=False, encoding='utf-8')
        try:
            temp_local.write(new_content)
            temp_local.close()
            
            # Push to device temp location
            temp_remote = "/data/local/tmp/mapworld_config_temp.json"
            push_cmd = f'adb -s {device_id} push "{temp_local.name}" {temp_remote}'
            push_result = subprocess.run(push_cmd, shell=True, capture_output=True, text=True, timeout=10)
            
            if push_result.returncode != 0:
                return False, f"Failed to push config to device: {push_result.stderr}"
            
            # Move temp file to final location with root permissions
            move_cmd = f'adb -s {device_id} shell "su -c \'cp {temp_remote} {config_path} && chmod 660 {config_path} && rm -f {temp_remote}\'"'
            move_result = subprocess.run(move_cmd, shell=True, capture_output=True, text=True, timeout=10)
            
            if move_result.returncode != 0:
                return False, f"Failed to move config on device: {move_result.stderr}"
            
            log("Successfully wrote DiscordData token to device (valid JSON)", device_id, "CONFIG")
            return True, ""
            
        finally:
            # Clean up local temp file
            try:
                os.unlink(temp_local.name)
            except:
                pass
        
    except subprocess.TimeoutExpired:
        return False, "Timeout while writing to device"
    except Exception as e:
        return False, f"Error writing token to device: {str(e)}"
def write_device_furtif_config(device_id: str, config_updates: dict) -> Tuple[bool, str]:
    """
    Writes Rotom/Furtif config fields to the MapWorld config on the device.
    ONLY works with valid JSON config files.
    If the config is invalid JSON, it will be DELETED so MapWorld creates a fresh one.

    Args:
        device_id: Device identifier
        config_updates: Dict of fields to update in the device config

    Returns:
        Tuple[bool, str]: (success, error_message)
        Special error: "INVALID_CONFIG_DELETED" means the config was deleted and needs recreation
    """
    device_id = format_device_id(device_id)
    config_path = "/data/data/com.github.furtif.furtifformaps/files/config.json"

    try:
        read_cmd = f'adb -s {device_id} shell "su -c \'base64 {config_path}\'"'
        result = subprocess.run(read_cmd, shell=True, capture_output=True, text=True, timeout=10)

        if result.returncode != 0 or not result.stdout:
            return False, f"Could not read config from device: {result.stderr}"

        try:
            raw_output = base64.b64decode(result.stdout.strip()).decode('utf-8').strip()
        except Exception as decode_err:
            log(f"Base64 decode failed, falling back to raw output: {decode_err}", device_id, "CONFIG")
            raw_output = result.stdout.strip()

        if not raw_output or '{' not in raw_output:
            return False, "Config file is empty or invalid"

        json_start = raw_output.find('{')
        json_end = raw_output.rfind('}')

        if json_start == -1 or json_end == -1:
            return False, "Could not find JSON boundaries in config"

        config_content = raw_output[json_start:json_end + 1]

        try:
            device_config = json.loads(config_content)
            log("Config parsed as valid JSON", device_id, "CONFIG")
        except json.JSONDecodeError as e:
            log(f"Config is NOT valid JSON: {e}", device_id, "ERROR")
            log("DELETING invalid config - MapWorld must create a new one", device_id, "CONFIG")
            delete_cmd = f'adb -s {device_id} shell "su -c \'rm -f {config_path}\'"'
            delete_result = subprocess.run(delete_cmd, shell=True, capture_output=True, text=True, timeout=10)
            if delete_result.returncode == 0:
                log("Invalid config file deleted successfully", device_id, "CONFIG")
                return False, "INVALID_CONFIG_DELETED"
            else:
                return False, f"Config is invalid JSON and could not be deleted: {delete_result.stderr}"

        device_config.update(config_updates)

        new_content = json.dumps(device_config, ensure_ascii=True)

        try:
            verify = json.loads(new_content)
            log(f"Output verified: valid JSON with {len(verify)} keys", device_id, "CONFIG")
        except json.JSONDecodeError as e:
            return False, f"Safety check failed: Output is not valid JSON: {e}"

        temp_local = tempfile.NamedTemporaryFile(mode='w', suffix='.json', delete=False, encoding='utf-8')
        try:
            temp_local.write(new_content)
            temp_local.close()

            temp_remote = "/data/local/tmp/mapworld_config_temp.json"
            push_cmd = f'adb -s {device_id} push "{temp_local.name}" {temp_remote}'
            push_result = subprocess.run(push_cmd, shell=True, capture_output=True, text=True, timeout=10)

            if push_result.returncode != 0:
                return False, f"Failed to push config to device: {push_result.stderr}"

            move_cmd = f'adb -s {device_id} shell "su -c \'cp {temp_remote} {config_path} && chmod 660 {config_path} && rm -f {temp_remote}\'"'
            move_result = subprocess.run(move_cmd, shell=True, capture_output=True, text=True, timeout=10)

            if move_result.returncode != 0:
                return False, f"Failed to move config on device: {move_result.stderr}"

            log("Successfully wrote Rotom config to device", device_id, "CONFIG")
            return True, ""

        finally:
            try:
                os.unlink(temp_local.name)
            except:
                pass

    except subprocess.TimeoutExpired:
        return False, "Timeout while writing to device"
    except Exception as e:
        return False, f"Error writing config to device: {str(e)}"
async def ensure_device_token(device_id: str, max_retries: int = 3) -> Tuple[bool, str, dict]:
    from .update import stop_apps
    """
    Ensures the device has the correct DiscordData token before starting MapWorld.
    First validates the token against the API, then compares with device and syncs if needed.
    If token validation fails, sends Discord notification and blocks app startup.

    Args:
        device_id: Device identifier
        max_retries: Number of retry attempts if writing fails

    Returns:
        Tuple[bool, str, dict]: (success, error_message, furtif_config)
    """
    device_id = format_device_id(device_id)
    
    # Load the stored token from Rotomina config
    config = load_config()
    stored_token = config.get("device_token", "").strip()
    
    # If no token is configured, skip the check
    if not stored_token:
        log("No device token configured, skipping token check", device_id, "CONFIG")
        return True, "", {}
    
    # Get device details for Discord notification
    device_details = get_device_details(device_id)
    device_name = device_details.get("display_name", device_id.split(":")[0] if ":" in device_id else device_id)
    
    # Validate token against API before proceeding
    log("Validating device token against API", device_id, "CONFIG")
    is_valid, message = await validate_device_token(stored_token)
    
    if not is_valid:
        log(f"Token validation failed: {message}", device_id, "ERROR")
        
        # Send Discord notification about invalid token
        await notify_invalid_token(device_name, device_id, message)
        
        return False, f"Token validation failed: {message}", {}
    
    log(f"Token validated successfully: {message}", device_id, "CONFIG")
    
    # Read current config from device
    furtif_config = read_device_furtif_config(device_id)
    
    if not furtif_config:
        log("Could not read device config, will attempt to write token anyway", device_id, "CONFIG")
        device_token = ""
    else:
        device_token = furtif_config.get("DiscordData", "").strip()
    
    # Compare tokens (both should have normal '=' after JSON parsing)
    if device_token == stored_token:
        log("Device token matches stored token, no update needed", device_id, "CONFIG")
        return True, "", furtif_config
    
    # Tokens don't match, need to write the correct token
    log(f"Device token mismatch, updating device config", device_id, "CONFIG")
    
    for attempt in range(max_retries):
        success, error = write_device_discord_token(device_id, stored_token)
        
        if success:
            # Verify the write was successful
            await asyncio.sleep(1)
            verify_config = read_device_furtif_config(device_id)
            if verify_config and verify_config.get("DiscordData", "").strip() == stored_token:
                log("Token successfully written and verified", device_id, "CONFIG")
                return True, "", verify_config
            else:
                log(f"Token verification failed, attempt {attempt + 1}/{max_retries}", device_id, "ERROR")
        
        elif error == "INVALID_CONFIG_DELETED":
            # Special case: config was invalid JSON and has been deleted
            # We need to start MapWorld briefly so it creates a new valid config
            log("Invalid config was deleted, starting MapWorld to create new config", device_id, "CONFIG")
            
            # Start MapWorld app (just launch it, don't do full login flow)
            start_cmd = f'adb -s {device_id} shell "am start -n com.github.furtif.furtifformaps/com.github.furtif.furtifformaps.MainActivity"'
            subprocess.run(start_cmd, shell=True, capture_output=True, text=True, timeout=10)
            
            # Wait for app to create config
            log("Waiting 10 seconds for MapWorld to create new config", device_id, "CONFIG")
            await asyncio.sleep(10)
            
            # Stop MapWorld
            await stop_apps(device_id, stop_pogo=False)
            
            # Now try to write the token again
            log("Retrying token write after config recreation", device_id, "CONFIG")
            success_retry, error_retry = write_device_discord_token(device_id, stored_token)
            
            if success_retry:
                # Verify
                await asyncio.sleep(1)
                verify_config = read_device_furtif_config(device_id)
                if verify_config and verify_config.get("DiscordData", "").strip() == stored_token:
                    log("Token successfully written after config recreation", device_id, "CONFIG")
                    return True, "", verify_config
            
            log(f"Token write failed after config recreation: {error_retry}", device_id, "ERROR")
        else:
            log(f"Failed to write token (attempt {attempt + 1}/{max_retries}): {error}", device_id, "ERROR")
        
        if attempt < max_retries - 1:
            await asyncio.sleep(2)
    
    return False, f"Failed to update device token after {max_retries} attempts", {}
def get_device_details(device_id: str) -> dict:
    from .update import version_manager
    """
    Optimized version of get_device_details that uses VersionManager
    to minimize ADB calls for version information.
    
    Furtif config handling:
    - If no furtif_config stored yet: Read once from device and save
    - If furtif_config already stored: Use stored config (no device read)
    - Fresh config is read on every app start in optimized_app_start()
    """
    try:
        config_data = load_config()
        device = next((d for d in config_data["devices"] if d["ip"] == device_id), None)
        is_new_device = device is None

        if not device:
            if ":" in device_id:
                display_name = device_id.split(":")[0]
            else:
                display_name = f"Device-{device_id[-4:]}" if len(device_id) > 4 else device_id
                
            device = {"ip": device_id, "display_name": display_name}
            config_data["devices"].append(device)
            save_config(config_data)

        details = {
            "display_name": device.get("display_name", device_id),
            "pogo_version": "N/A",
            "mitm_version": "N/A",
            "module_version": "N/A"
        }

        # Check if furtif_config is already stored
        stored_furtif_config = device.get("furtif_config", {})
        
        # If new device or no stored config yet, read from device once
        if is_new_device or not stored_furtif_config:
            log("Reading Furtif config (first time or missing)", device_id, "CONFIG")
            furtif_config = read_device_furtif_config(device_id)
            if furtif_config:
                stored_furtif_config = furtif_config
                # Update display_name from fresh config
                new_name = furtif_config.get("RotomDeviceName", "").strip()
                if new_name:
                    device["display_name"] = new_name
                    details["display_name"] = new_name
        else:
            # Use stored config, update display_name if needed
            stored_name = stored_furtif_config.get("RotomDeviceName", "").strip()
            if stored_name and stored_name != device.get("display_name"):
                device["display_name"] = stored_name
                details["display_name"] = stored_name

        # Get version info from VersionManager
        version_info = version_manager.get_version_info(device_id)
        if version_info:
            details["pogo_version"] = version_info.get("pogo_version", "N/A")
            details["mitm_version"] = version_info.get("mitm_version", "N/A")
            details["module_version"] = version_info.get("module_version", "N/A")

        # Save details and furtif_config (if we read a new one)
        update_device_info(device_id, details, stored_furtif_config if stored_furtif_config else None)
        return details
    except Exception as e:
        log(f"Device detail error: {str(e)}", device_id, "ERROR")
        return {
            "display_name": device.get("display_name", device_id.split(":")[0] if ":" in device_id else device_id) if device else device_id,
            "pogo_version": "N/A",
            "mitm_version": "N/A",
            "module_version": "N/A"
        }
