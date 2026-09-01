"""Shared mutable runtime state"""
import threading


device_status_cache = {}
update_lock = threading.Lock()
update_in_progress = False
current_progress = 0
devices_in_update = {}  # Format: {device_id: {"in_update": True, "update_type": "pogo/mitm/pif", "started_at": timestamp}}
device_runtimes = {}
device_setup_tasks = {}  # {setup_id: {device_id, step, step_label, progress, error, needs_auth, completed, results}}
_display_name_cache = {}
_display_name_cache_lock = threading.Lock()
_discord_bot_client: "discord.Client | None" = None
github_api_cache = {}
GITHUB_CACHE_TTL = 3600  # 1 hour cache
def update_progress(progress: int):
    """
    Updates the global progress indicator for UI updates
    
    Args:
        progress: Integer value between 0-100 representing progress percentage
    """
    global current_progress
    current_progress = progress
