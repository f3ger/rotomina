"""Low-level helpers and logging"""
from functools import wraps
import datetime
import re
import time

from .state import _display_name_cache, _display_name_cache_lock

def log(message: str, device_id: str = None, category: str = "INFO"):
    from .config import load_config
    """Unified log output with timestamp and device assignment."""
    timestamp = datetime.datetime.now().strftime("%H:%M:%S")

    if device_id:
        device_id = format_device_id(device_id)
        with _display_name_cache_lock:
            if device_id not in _display_name_cache:
                config = load_config()
                device = next((d for d in config.get("devices", []) if d["ip"] == device_id), None)
                _display_name_cache[device_id] = device.get("display_name") if device else device_id.split(":")[0]
            tag = _display_name_cache[device_id]
    else:
        tag = "--SYSTEM--"

    print(f"[{timestamp}] [{tag}] [{category}] {message}")
def clear_display_name_cache(device_id: str = None):
    """Clear cache when display_name is changed."""
    with _display_name_cache_lock:
        if device_id:
            _display_name_cache.pop(format_device_id(device_id), None)
        else:
            _display_name_cache.clear()
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
        log(f"Error parsing version '{v}': {e}", None, "ERROR")
        return ()
def format_memory(mem_kb: int) -> str:
    """
    Converts memory values to readable formats
    Input value is in KB (not Bytes)!
    """
    try:
        if not mem_kb:
            return "N/A"
            
        size = float(mem_kb)
        
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
