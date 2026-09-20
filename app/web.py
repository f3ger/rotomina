"""FastAPI web app: routes, pages, websockets"""
from contextlib import asynccontextmanager
from fastapi import FastAPI, Request, Form, WebSocket, WebSocketDisconnect, HTTPException, UploadFile, File
from fastapi.responses import HTMLResponse, RedirectResponse, JSONResponse
from fastapi.staticfiles import StaticFiles
from pathlib import Path
from starlette.middleware.sessions import SessionMiddleware
from starlette.templating import Jinja2Templates
from typing import List, Optional
from uuid import uuid4
import asyncio
import httpx
import re
import shutil
import subprocess
import sys
import threading
import time
import zipfile

from . import state
from .adb import adb_pool, check_adb_connection, sync_system_adb_key
from .config import APK_DIR, BASE_DIR, DEFAULT_ARCH, EXTRACT_DIR, POGO_MIRROR_URL, S_APK_DIR, TimeoutConfig, load_config, needs_setup, save_config
from .devices import get_device_details, get_device_package_name, read_device_furtif_config, validate_device_token, write_device_furtif_config
from .discord_bot import DISCORD_BOT_AVAILABLE, DISCORD_IMPORT_ERROR, start_discord_bot
from .state import device_setup_tasks, device_status_cache, devices_in_update, update_progress
from .update import clear_github_api_cache, download_apk, download_module_version, ensure_latest_apk_downloaded, extract_pogo_version_from_apkm, fetch_available_module_versions, get_all_module_versions_for_ui, get_available_local_google_versions, get_available_local_versions, get_available_mitm_versions, get_available_samsung_versions, get_available_versions, get_pif_versions_for_ui, get_status_data, install_module_with_progress, mapworld_update_task, mark_device_in_update, optimized_app_start, optimized_device_monitoring, optimized_module_update_task, optimized_perform_installation, optimized_pogo_update_task, perform_installations, run_device_setup, run_device_setup_from_step, scheduled_update_task, stop_apps, unzip_apk, update_api_status, version_manager, ws_manager
from .utils import format_device_id, format_memory, log

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
async def get_status_data_with_tailwind_classes(apk_type: str = "google"):
    """Enhanced version of get_status_data that adds Tailwind CSS-specific class information"""
    data = await get_status_data(apk_type)
    
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
    asyncio.create_task(start_discord_bot())
    yield
app = FastAPI(lifespan=lifespan)
app.add_middleware(SessionMiddleware, secret_key="CHANGE_ME_TO_A_SECURE_KEY")
app.mount("/static", StaticFiles(directory=str(BASE_DIR / "static")), name="static")
templates = Jinja2Templates(directory=str(BASE_DIR / "templates"))
templates.env.filters['format_memory'] = format_memory
templates.env.globals.update({
    'check_adb_connection': check_adb_connection,
    'get_device_display_name': lambda ip: get_device_details(ip)["display_name"],
    'get_available_versions': get_available_versions
})
@app.get("/discord-bot/status")
async def discord_bot_status_endpoint(request: Request):
    if redirect := require_login(request):
        return redirect
    if not DISCORD_BOT_AVAILABLE:
        return JSONResponse({"status": "not_installed", "error": DISCORD_IMPORT_ERROR, "python_path": sys.executable})
    cfg = load_config()
    if not cfg.get("discord_bot_token", "").strip():
        return JSONResponse({"status": "no_token"})
    if state._discord_bot_client is None:
        return JSONResponse({"status": "offline"})
    if not state._discord_bot_client.is_ready():
        return JSONResponse({"status": "connecting"})
    return JSONResponse({"status": "online", "username": str(state._discord_bot_client.user)})
@app.post("/discord-bot/restart")
async def discord_bot_restart_endpoint(request: Request):
    if redirect := require_login(request):
        return redirect
    if state._discord_bot_client is not None:
        await state._discord_bot_client.close()
        state._discord_bot_client = None
    asyncio.create_task(start_discord_bot())
    return JSONResponse({"status": "restarting"})
@app.websocket("/ws/status")
async def websocket_endpoint(websocket: WebSocket):
    """Optimized WebSocket endpoint with connection pooling"""
    await ws_manager.connect(websocket)
    
    try:
        while True:
            # Receive message with timeout
            try:
                message = await asyncio.wait_for(websocket.receive_text(), timeout=30.0)
                
                # Handle different message types
                if message == "refresh":
                    # Send current status without creating new connection
                    status_data = await get_status_data()
                    await websocket.send_json(status_data)
                    
                elif message == "ping":
                    await websocket.send_text("pong")
                    
                else:
                    # Unknown message, log and continue
                    log(f"Unknown WebSocket message: {message}", None, "DEBUG")
                    
                    # Refresh specific device data
                    device_ip = message.split(":", 1)[1]
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
        log(f"WebSocket error: {e}", None, "ERROR")
        ws_manager.disconnect(websocket)
@app.get("/", response_class=HTMLResponse)
def root(request: Request):
    if is_logged_in(request):
        return RedirectResponse(url="/status")
    return RedirectResponse(url="/login")
@app.get("/login", response_class=HTMLResponse)
def login_page(request: Request):
    if needs_setup():
        return templates.TemplateResponse(request, "login.html", {"setup_mode": True})
    return templates.TemplateResponse(request, "login.html")
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
    return templates.TemplateResponse(request, "login.html", {
        "error": "Invalid credentials"
    })
@app.post("/setup")
def setup_action(request: Request, username: str = Form(...), password: str = Form(...), password_confirm: str = Form(...)):
    if not needs_setup():
        raise HTTPException(status_code=403, detail="Setup already completed")

    errors = []
    if not username.strip():
        errors.append("Username is required")
    if len(password) < 4:
        errors.append("Password must be at least 4 characters")
    if password != password_confirm:
        errors.append("Passwords do not match")

    if errors:
        return templates.TemplateResponse(request, "login.html", {
            "setup_mode": True,
            "error": ". ".join(errors)
        })

    config = load_config()
    config["users"].append({"username": username.strip(), "password": password})
    save_config(config)

    request.session["logged_in"] = True
    request.session["username"] = username.strip()
    log(f"Initial admin account '{username.strip()}' created via setup wizard", None, "CONFIG")
    return RedirectResponse(url="/status", status_code=303)
@app.get("/logout")
def logout_action(request: Request):
    request.session.clear()
    return RedirectResponse(url="/login")
@app.get("/status", response_class=HTMLResponse)
async def status_page(request: Request, apk_type: str = "google"):
    if redirect := require_login(request):
        return redirect

    config = load_config()
    devices = []

    # Validate apk_type parameter
    if apk_type not in ("google", "samsung"):
        apk_type = "google"

    # Check if token is valid - get device_token (main field)
    token_valid = False
    device_token = config.get("device_token", "")

    if device_token:
        try:
            is_valid, message = await validate_device_token(device_token)
            token_valid = is_valid
            log(f"Token validation result in status: {is_valid}, message: {message}", None, "CONFIG")
        except Exception as e:
            log(f"Error validating token in status: {e}", None, "ERROR")
            token_valid = False
    
    # Get local PoGo versions from local APK directories only
    log(f"Status page requested with apk_type={apk_type}", None, "DEBUG")
    versions = get_available_local_versions("all")
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
        formatted_ip = format_device_id(ip)
        if formatted_ip in devices_in_update and devices_in_update[formatted_ip]["in_update"]:
            in_update = True
            update_type = devices_in_update[formatted_ip]["update_type"]
            update_duration = int(time.time() - devices_in_update[formatted_ip]["started_at"])
            update_info = f"{update_type} ({update_duration}s)"
        
        mem_free_value = status.get("mem_free", 0)
        
        devices.append({
            "display_name": details.get("display_name", ip.split(":")[0]),
            "ip": ip,
            "status": check_adb_connection(ip)[0],
            "is_alive": status["is_alive"],
            "pogo": details.get("pogo_version", "N/A"),
            "mitm": details.get("mitm_version", "N/A"),
            "module": details.get("module_version", "N/A"),
            "mem_free": mem_free_value,
            "last_update": status["last_update"],
            "control_enabled": dev.get("control_enabled", False),
            "in_update": in_update,
            "update_info": update_info
        })
    
    return templates.TemplateResponse(request, "status.html", {
        "username": request.session.get("username", ""),
        "devices": devices,
        "config": config,
        "token_valid": token_valid,
        "now": time.time(),
        "pogo_latest": pogo_latest,
        "pogo_previous": pogo_previous,
        "apk_type": apk_type
    })
@app.get("/settings", response_class=HTMLResponse)
async def settings_page(request: Request):
    if redirect := require_login(request):
        return redirect

    config = load_config()

    # Check if token is valid - get device_token (main field)
    token_valid = False
    device_token = config.get("device_token", "")

    if device_token:
        try:
            is_valid, message = await validate_device_token(device_token)
            token_valid = is_valid
            log(f"Token validation result: {is_valid}, message: {message}", None, "CONFIG")
        except Exception as e:
            log(f"Error validating token in settings: {e}", None, "ERROR")
            token_valid = False
    
    return templates.TemplateResponse(request, "settings.html", {
        "config": config,
        "token_valid": token_valid
    })
@app.post("/settings/save-api", response_class=HTMLResponse)
def settings_save_api(
    request: Request,
    rotomApiUrl: str = Form(""),
    rotomApiUser: str = Form(""),
    rotomApiPass: str = Form(""),
):
    if redirect := require_login(request):
        return redirect

    config = load_config()
    config.update({
        "rotomApiUrl": rotomApiUrl,
        "rotomApiUser": rotomApiUser,
        "rotomApiPass": rotomApiPass,
    })

    save_config(config)
    log(f"API settings saved successfully", None, "CONFIG")

    return RedirectResponse(url="/settings?success=API settings saved", status_code=302)
@app.post("/settings/save-discord", response_class=HTMLResponse)
def settings_save_discord(
    request: Request,
    discord_webhook_url: str = Form(""),
    discord_bot_token: str = Form(""),
    discord_bot_channel_id: str = Form(""),
    discord_bot_role_id: str = Form(""),
    discord_bot_notify_channel_id: str = Form(""),
):
    if redirect := require_login(request):
        return redirect

    config = load_config()
    config.update({
        "discord_webhook_url": discord_webhook_url,
        "discord_bot_token": discord_bot_token,
        "discord_bot_channel_id": discord_bot_channel_id,
        "discord_bot_role_id": discord_bot_role_id,
        "discord_bot_notify_channel_id": discord_bot_notify_channel_id,
    })

    save_config(config)
    log(f"Discord settings saved successfully", None, "CONFIG")

    return RedirectResponse(url="/settings?success=Discord settings saved", status_code=302)
@app.post("/settings/save-device-token", response_class=HTMLResponse)
async def save_device_token(request: Request, device_token: str = Form("")):
    """Saves the device token to config.json after validation"""
    log(f"DEBUG: save_device_token called with token '{device_token[:20]}...'", None, "CONFIG")
    if redirect := require_login(request):
        log(f"DEBUG: require_login returned redirect", None, "CONFIG")
        return redirect
    
    token = device_token.strip()
    
    # Validate token if provided
    if token:
        try:
            is_valid, message = await validate_device_token(token, bypass_cache=True)
            if not is_valid:
                log(f"Token validation failed: {message}", None, "ERROR")
                return RedirectResponse(url=f"/settings?error=Invalid token: {message}", status_code=302)
            log(f"Token validation successful: {message}", None, "CONFIG")
        except Exception as e:
            log(f"Error validating token: {e}", None, "ERROR")
            return RedirectResponse(url=f"/settings?error=Token validation error: {e}", status_code=302)
    
    # Save token to config and distribute to ALL devices
    config = load_config()
    config["device_token"] = token

    devices = config.get("devices", [])
    if devices:
        for i, device in enumerate(devices):
            if "furtif_config" not in device:
                device["furtif_config"] = {}
            device["furtif_config"]["DiscordData"] = token
        log(f"Token saved and auto-distributed to {len(devices)} device(s)", None, "CONFIG")
        save_config(config)
    else:
        log("No devices found to save DiscordData", None, "ERROR")
        return RedirectResponse(url="/settings?error=No devices found to save token", status_code=302)
    
    log(f"Device token saved ({len(token)} chars)", None, "CONFIG")
    
    if token:
        return RedirectResponse(url="/settings?success=Device token validated and saved successfully", status_code=302)
    else:
        return RedirectResponse(url="/settings?success=Device token cleared", status_code=302)
@app.get("/devices/rotom-config")
def get_device_rotom_config(request: Request, ip: str = ""):
    """Returns the current Rotom/Furtif config for a device.
    Reads live from the device via ADB; falls back to the stored config on error."""
    if require_login(request):
        return JSONResponse({"error": "Unauthorized"}, status_code=401)

    config = load_config()
    target_device = next((d for d in config.get("devices", []) if d["ip"] == ip), None)
    if not target_device:
        return JSONResponse({"error": "Device not found"}, status_code=404)

    live_config = read_device_furtif_config(ip)
    if live_config:
        if "furtif_config" not in target_device:
            target_device["furtif_config"] = {}
        target_device["furtif_config"].update(live_config)
        save_config(config)
        return JSONResponse(live_config)

    return JSONResponse(target_device.get("furtif_config", {}))
@app.post("/devices/save-rotom-config", response_class=HTMLResponse)
def save_device_rotom_config(
    request: Request,
    device_ip: str = Form(""),
    IsRotomMode: str = Form("off"),
    RotomSecret: str = Form(""),
    RotomURL: str = Form(""),
    RotomDeviceName: str = Form(""),
    RotomDelayLoader: int = Form(3),
    RotomMaxWorkers: int = Form(60),
    RotomTryAutoStart: str = Form("off"),
    RotomRpcJailMode: str = Form("off"),
    RotomCheckPgoForced: str = Form("off"),
    RotomUsesCmds: str = Form("off"),
    RotomIgnoreUnity: str = Form("off"),
    RotomIgnoreDelays: str = Form("off"),
    RotomUseRealPublicIp: str = Form("off"),
    PackageName: str = Form("com.nianticlabs.pokemongo"),
    restart_device: str = Form("off"),
):
    if redirect := require_login(request):
        return redirect

    # Server-side validation
    RotomDelayLoader = max(3, min(30, RotomDelayLoader))
    RotomMaxWorkers = max(1, min(250, RotomMaxWorkers))
    if PackageName not in ("com.nianticlabs.pokemongo", "com.nianticlabs.pokemongo.ares"):
        PackageName = "com.nianticlabs.pokemongo"

    config = load_config()
    target_device = None
    for device in config.get("devices", []):
        if device["ip"] == device_ip:
            target_device = device
            break

    if not target_device:
        return RedirectResponse(url="/settings?error=Device not found", status_code=302)

    rotom_fields = {
        "IsRotomMode": IsRotomMode == "on",
        "RotomSecret": RotomSecret,
        "RotomURL": RotomURL,
        "RotomDeviceName": RotomDeviceName,
        "RotomDelayLoader": RotomDelayLoader,
        "RotomMaxWorkers": RotomMaxWorkers,
        "RotomTryAutoStart": RotomTryAutoStart == "on",
        "RotomRpcJailMode": RotomRpcJailMode == "on",
        "RotomCheckPgoForced": RotomCheckPgoForced == "on",
        "RotomUsesCmds": RotomUsesCmds == "on",
        "RotomIgnoreUnity": RotomIgnoreUnity == "on",
        "RotomIgnoreDelays": RotomIgnoreDelays == "on",
        "RotomUseRealPublicIp": RotomUseRealPublicIp == "on",
        "PackageName": PackageName,
    }

    if "furtif_config" not in target_device:
        target_device["furtif_config"] = {}
    target_device["furtif_config"].update(rotom_fields)

    save_config(config)
    log(f"Rotom config saved for device {device_ip}", None, "CONFIG")

    success, error_msg = write_device_furtif_config(device_ip, rotom_fields)
    
    # Restart device if checkbox is checked
    if restart_device == "on":
        if IsRotomMode == "on":
            log(f"Restarting apps after config save (Rotom mode)", None, "CONFIG")
            try:
                device_id = format_device_id(device_ip)
                control_enabled = target_device.get("control_enabled", False)
                async def restart_apps_task():
                    await optimized_app_start(device_id, control_enabled)
                import threading
                threading.Thread(target=lambda: asyncio.run(restart_apps_task())).start()
                restart_msg = " and apps restart triggered"
            except Exception as e:
                log(f"Failed to restart apps {device_ip}: {e}", None, "ERROR")
                restart_msg = " (apps restart failed)"
        else:
            log(f"Killing all apps after config save (not Rotom mode)", None, "CONFIG")
            try:
                device_id = format_device_id(device_ip)
                # Kill both POGO and MapWorld using adb commands directly
                pogo_package = get_device_package_name(device_id)
                kill_cmd = f"am force-stop {pogo_package}; am force-stop com.github.furtif.furtifformaps"
                adb_pool.execute_command(device_id, ["adb", "shell", kill_cmd])
                restart_msg = " and all apps killed"
            except Exception as e:
                log(f"Failed to kill apps {device_ip}: {e}", None, "ERROR")
                restart_msg = " (apps kill failed)"
    else:
        restart_msg = ""
    
    if success:
        return RedirectResponse(url=f"/settings?success=Rotom config saved and pushed to device{restart_msg}", status_code=302)
    else:
        log(f"Failed to push rotom config to device {device_ip}: {error_msg}", None, "ERROR")
        encoded_error = error_msg.replace("&", "%26").replace("=", "%3D")
        return RedirectResponse(url=f"/settings?success=Rotom config saved (ADB push failed: {encoded_error})", status_code=302)
@app.post("/devices/add")
async def add_device(request: Request, new_ip: str = Form(...)):
    if redirect := require_login(request):
        return redirect

    device_id = format_device_id(new_ip.strip())
    log(f"Adding device", device_id, "CONFIG")

    config = load_config()
    if not any(dev["ip"] == device_id for dev in config["devices"]):
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

    # Start automatic device setup pipeline
    setup_id = str(uuid4())
    device_setup_tasks[setup_id] = {
        "device_id": device_id,
        "step": "pending",
        "step_label": "Starting setup...",
        "progress": 0,
        "error": None,
        "needs_auth": False,
        "completed": False,
        "results": {}
    }
    asyncio.create_task(run_device_setup(setup_id, device_id))

    return JSONResponse({"setup_id": setup_id, "device_id": device_id})
@app.get("/devices/setup-status/{setup_id}")
def get_setup_status(setup_id: str):
    task = device_setup_tasks.get(setup_id)
    if not task:
        return JSONResponse({"error": "Setup not found"}, status_code=404)
    return JSONResponse(task)
@app.post("/devices/setup-retry-auth/{setup_id}")
async def retry_setup_auth(setup_id: str):
    task = device_setup_tasks.get(setup_id)
    if not task:
        return JSONResponse({"error": "Setup not found"}, status_code=404)

    task["needs_auth"] = False
    task["error"] = None
    task["step_label"] = "Retrying ADB connection..."
    task["progress"] = 5

    # Clear ADB cache so fresh connection attempt is made
    check_adb_connection.cache_clear()

    device_id = task["device_id"]
    asyncio.create_task(run_device_setup_from_step(setup_id, device_id, "adb_connect"))

    return JSONResponse({"status": "retry_started"})
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

    device_id = format_device_id(device_ip)
    
    if redirect := require_login(request):
        return redirect
    
    try:
        state.update_in_progress = True
        update_progress(10)
        
        versions = await fetch_available_module_versions(module_type)
        update_progress(20)
        
        target_version = None
        for ver in versions:
            if ver["version"] == version and ver["module_type"] == module_type:
                target_version = ver
                break
        
        if not target_version:
            state.update_in_progress = False
            state.current_progress = 0
            return RedirectResponse(url=f"/status?error=Module version {version} not found", status_code=302)
        
        update_progress(30)
        
        update_progress(40)
        module_file = await download_module_version(target_version)
        update_progress(50)
        
        if not module_file:
            state.update_in_progress = False
            state.current_progress = 0
            return RedirectResponse(url=f"/status?error=Failed to download module version", status_code=302)
        
        update_progress(60)
        
        success = await install_module_with_progress(device_ip, module_file, module_type)
        
        if success:
            return RedirectResponse(url="/status?success=Module update completed", status_code=302)
        else:
            return RedirectResponse(url="/status?error=Module update failed", status_code=302)
            
    except Exception as e:
        log(f"Error updating to module version {version}: {str(e)}", device_ip, "ERROR")
        state.update_in_progress = False
        state.current_progress = 0
        return RedirectResponse(url="/status?error=Module update failed", status_code=302)
@app.post("/mitm/device-update")
async def mitm_device_update(request: Request, device_ip: str = Form(...), version: str = Form(...), apk_path: str = Form(...)):
    if redirect := require_login(request):
        return redirect

    device_id = format_device_id(device_ip)

    try:
        apk_file = Path(apk_path)
        if not apk_file.exists():
            return {"success": False, "error": f"APK file not found: {apk_path}"}

        log(f"Installing MITM version {version} on device {device_id}", device_id, "UPDATE")

        # Stop MapWorld
        await stop_apps(device_id, stop_pogo=False, stop_mapworld=True)

        # Install the MITM APK
        install_cmd = f'adb -s {device_id} install -r "{apk_file}"'
        result = subprocess.run(install_cmd, shell=True, capture_output=True, text=True, timeout=TimeoutConfig.LONG)

        if result.returncode == 0:
            log(f"MITM version {version} installed successfully on device {device_id}", device_id, "UPDATE")
            return {"success": True, "message": f"MITM updated to v{version}"}
        else:
            log(f"Failed to install MITM version {version}: {result.stderr}", device_id, "ERROR")
            return {"success": False, "error": result.stderr}

    except Exception as e:
        log(f"Error updating MITM on device {device_id}: {str(e)}", device_id, "ERROR")
        return {"success": False, "error": str(e)}
@app.post("/pogo/device-update", response_class=HTMLResponse)
async def pogo_device_update(request: Request, device_ip: str = Form(...), version: str = Form(...), apk_type: str = Form("google")):
    if redirect := require_login(request):
        return redirect

    # Validate apk_type
    if apk_type not in ("google", "samsung"):
        apk_type = "google"

    device_id = format_device_id(device_ip)
    versions = get_available_versions(apk_type)
    target_version = None
    
    for version_type in ["latest", "previous"]:
        if version_type in versions and versions[version_type].get("version") == version:
            target_version = versions[version_type]
    
    if not target_version and apk_type == "google":
        # For Google, try checking mirror
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
                            "arch": DEFAULT_ARCH,
                            "apk_type": "google"
                        }
                        break
        except Exception as e:
            log(f"Error checking all versions: {str(e)}", None, "ERROR")
    
    if not target_version:
        # Fallback: check for locally uploaded APK
        if apk_type == "samsung":
            local_filename = f"com.nianticlabs.pokemongo_{DEFAULT_ARCH}_{version}.apk"
            local_path = S_APK_DIR / local_filename
        else:
            local_filename = f"com.nianticlabs.pokemongo_{DEFAULT_ARCH}_{version}.apkm"
            local_path = APK_DIR / local_filename
            
        if local_path.exists():
            target_version = {
                "version": version,
                "filename": local_filename,
                "arch": DEFAULT_ARCH,
                "apk_type": apk_type
            }
            log(f"Using locally uploaded {apk_type.upper()} APK for version {version}", None, "UPDATE")

    if not target_version:
        return RedirectResponse(url="/status?error=Version not found", status_code=302)

    try:
        state.update_in_progress = True
        state.current_progress = 0

        # Mark device and broadcast immediately so UI shows spinner
        mark_device_in_update(device_ip, "pogo")
        status_data = await get_status_data(apk_type)
        await ws_manager.broadcast(status_data)

        if apk_type == "samsung":
            # Samsung: direct .apk installation (no extraction needed)
            apk_file = S_APK_DIR / target_version["filename"]
            if not apk_file.exists():
                # Try to download if URL available
                if "url" in target_version and target_version["url"]:
                    apk_file = download_apk(target_version)
                else:
                    return RedirectResponse(url=f"/status?error=Samsung APK file not found locally for version {version}", status_code=302)
            
            success = await optimized_perform_installation(device_ip, apk_file, "samsung")
        else:
            # Google: extract .apkm and install
            apk_file = APK_DIR / target_version["filename"]
            if not apk_file.exists():
                apk_file = download_apk(target_version)

            specific_extract_dir = EXTRACT_DIR / target_version["version"]
            specific_extract_dir.mkdir(parents=True, exist_ok=True)
            unzip_apk(apk_file, specific_extract_dir)

            success = await optimized_perform_installation(device_ip, specific_extract_dir, "google")

        if success:
            return RedirectResponse(url="/status?success=Pokemon GO updated successfully", status_code=302)
        else:
            return RedirectResponse(url="/status?error=Update failed", status_code=302)
    except Exception as e:
        log(f"Error updating to version {version}: {str(e)}", device_ip, "ERROR")
        return RedirectResponse(url="/status?error=Update failed", status_code=302)
    finally:
        state.update_in_progress = False
        state.current_progress = 0
@app.post("/pogo/update", response_class=HTMLResponse)
async def pogo_update(request: Request, apk_type: str = Form("google")):
    if redirect := require_login(request):
        return redirect
    
    # Validate apk_type
    if apk_type not in ("google", "samsung"):
        apk_type = "google"
    
    config = load_config()
    device_ips = [dev["ip"] for dev in config.get("devices", [])]
    
    versions = get_available_versions(apk_type)
    if not versions or not versions.get("latest"):
        return RedirectResponse(url=f"/status?error=No {apk_type} versions found", status_code=302)
    
    entry = versions["latest"]
    
    if apk_type == "samsung":
        # Samsung: direct .apk installation
        apk_file = S_APK_DIR / entry["filename"]
        if not apk_file.exists():
            if "url" in entry and entry["url"]:
                apk_file = download_apk(entry)
            else:
                return RedirectResponse(url=f"/status?error=Samsung APK not found locally for version {entry['version']}", status_code=302)
        
        # Install directly without extraction
        for device_ip in device_ips:
            await optimized_perform_installation(device_ip, apk_file, "samsung")
    else:
        # Google: extract .apkm and install
        apk_file = APK_DIR / entry["filename"]
        if not apk_file.exists():
            apk_file = download_apk(entry)
        
        version_extract_dir = EXTRACT_DIR / entry["version"]
        unzip_apk(apk_file, version_extract_dir)
        
        await perform_installations(device_ips, version_extract_dir, "google")
    
    return RedirectResponse(url="/status", status_code=302)
MAX_APK_UPLOAD_SIZE = 300 * 1024 * 1024  # 300 MB
@app.post("/pogo/upload-apk")
async def upload_pogo_apk(request: Request, file: UploadFile = File(...)):
    """Upload a .apkm (Google) or .apk (Samsung) file manually as fallback"""
    if redirect := require_login(request):
        return redirect

    if not file.filename:
        return JSONResponse(status_code=400, content={"success": False, "error": "No file provided"})
    
    filename_lower = file.filename.lower()
    is_apkm = filename_lower.endswith('.apkm')
    is_apk = filename_lower.endswith('.apk')
    
    if not (is_apkm or is_apk):
        return JSONResponse(status_code=400, content={"success": False, "error": "Only .apkm (Google) or .apk (Samsung) files are accepted"})

    try:
        content = await file.read()
        if len(content) > MAX_APK_UPLOAD_SIZE:
            return JSONResponse(status_code=400, content={"success": False, "error": f"File too large. Maximum size is {MAX_APK_UPLOAD_SIZE // (1024*1024)}MB"})
        if len(content) < 1024:
            return JSONResponse(status_code=400, content={"success": False, "error": "File is too small to be a valid APK"})
    except Exception as e:
        return JSONResponse(status_code=500, content={"success": False, "error": f"Failed to read uploaded file: {str(e)}"})

    # Determine target directory and type
    if is_apkm:
        target_dir = APK_DIR
        apk_type = "google"
        type_label = "G"
        ext = "apkm"
    else:
        target_dir = S_APK_DIR
        apk_type = "samsung"
        type_label = "S"
        ext = "apk"
    
    target_dir.mkdir(parents=True, exist_ok=True)
    temp_path = target_dir / f"_upload_temp_{uuid4().hex}.{ext}"

    try:
        with open(temp_path, "wb") as f:
            f.write(content)

        # Validate based on file type
        if is_apkm:
            try:
                with zipfile.ZipFile(temp_path, 'r') as zf:
                    apk_files = [f for f in zf.namelist() if f.endswith('.apk')]
                    if not apk_files:
                        return JSONResponse(status_code=400, content={"success": False, "error": "Invalid .apkm file: no .apk files found inside the archive"})
            except zipfile.BadZipFile:
                return JSONResponse(status_code=400, content={"success": False, "error": "Invalid file: not a valid ZIP/APKM archive"})
            
            try:
                version = extract_pogo_version_from_apkm(temp_path)
                log(f"Extracted version {version} from uploaded APKM", None, "UPDATE")
            except Exception as e:
                return JSONResponse(status_code=400, content={"success": False, "error": f"Could not extract version from APKM: {str(e)}"})
        else:
            # For Samsung APK, try to extract version from filename or use generic pattern
            version_match = re.search(r'(\d+\.\d+\.\d+)', file.filename)
            if version_match:
                version = version_match.group(1)
            else:
                return JSONResponse(status_code=400, content={"success": False, "error": "Could not extract version from APK filename. Format should be: com.nianticlabs.pokemongo_<arch>_<version>.apk"})

        target_filename = f"com.nianticlabs.pokemongo_{DEFAULT_ARCH}_{version}.{ext}"
        target_path = target_dir / target_filename

        if target_path.exists():
            temp_path.unlink(missing_ok=True)
            return JSONResponse(content={"success": True, "version": version, "apk_type": apk_type, "message": f"Version {version} ({type_label}) is already available", "already_exists": True})

        shutil.move(str(temp_path), str(target_path))
        log(f"Saved uploaded {type_label} APK as {target_filename}", None, "UPDATE")

        # Only extract for Google/APKM files
        if is_apkm:
            extract_dir = EXTRACT_DIR / version
            try:
                unzip_apk(target_path, extract_dir)
                log(f"Extracted uploaded APKM to {extract_dir}", None, "UPDATE")
            except Exception as e:
                log(f"Warning: Failed to pre-extract uploaded APKM: {e}", None, "WARNING")

        get_available_versions.cache_clear()

        try:
            status_data = await get_status_data()
            await ws_manager.broadcast(status_data)
        except Exception:
            pass

        return JSONResponse(content={"success": True, "version": version, "apk_type": apk_type, "filename": target_filename, "message": f"Version {version} ({type_label}) uploaded and ready for installation"})

    except Exception as e:
        log(f"APK upload error: {str(e)}", None, "ERROR")
        return JSONResponse(status_code=500, content={"success": False, "error": f"Upload failed: {str(e)}"})
    finally:
        if temp_path.exists():
            temp_path.unlink(missing_ok=True)
@app.get("/api/pogo-local-versions")
async def get_local_pogo_versions(request: Request, apk_type: str = "all"):
    """Returns list of locally available PoGO APK versions (Google APKM or Samsung APK)"""
    if redirect := require_login(request):
        return redirect

    versions = []

    # Get Google/APKM versions
    if apk_type in ("all", "google"):
        APK_DIR.mkdir(parents=True, exist_ok=True)
        for apkm_file in APK_DIR.glob("com.nianticlabs.pokemongo_*.apkm"):
            match = re.search(r'com\.nianticlabs\.pokemongo_[^_]+_(.+)\.apkm', apkm_file.name)
            if match:
                version = match.group(1)
                size_mb = round(apkm_file.stat().st_size / (1024 * 1024), 1)
                versions.append({
                    "version": version,
                    "filename": apkm_file.name,
                    "size_mb": size_mb,
                    "apk_type": "google",
                    "type_label": "G"
                })

    # Get Samsung/APK versions
    if apk_type in ("all", "samsung"):
        S_APK_DIR.mkdir(parents=True, exist_ok=True)
        for apk_file in S_APK_DIR.glob("com.nianticlabs.pokemongo_*.apk"):
            match = re.search(r'com\.nianticlabs\.pokemongo_[^_]+_(.+)\.apk', apk_file.name)
            if match:
                version = match.group(1)
                size_mb = round(apk_file.stat().st_size / (1024 * 1024), 1)
                versions.append({
                    "version": version,
                    "filename": apk_file.name,
                    "size_mb": size_mb,
                    "apk_type": "samsung",
                    "type_label": "S"
                })

    versions.sort(key=lambda x: [int(n) for n in x["version"].split(".")], reverse=True)
    return JSONResponse(content={"versions": versions})
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
@app.get("/api/module-sources")
def get_module_sources(request: Request):
    """Get all configured module sources"""
    if not is_logged_in(request):
        return {"error": "Not authenticated"}
    
    config = load_config()
    sources = config.get("pif_module_sources", [])
    return {"sources": sources}
def extract_repo_from_url(url_or_repo: str) -> str:
    """Extract owner/repo from a GitHub URL or return the input if already in correct format"""
    url_or_repo = url_or_repo.strip()
    
    # If it's already in owner/repo format
    if "/" in url_or_repo and not url_or_repo.startswith("http") and len(url_or_repo.split("/")) == 2:
        return url_or_repo
    
    # Extract from GitHub URL
    if "github.com" in url_or_repo:
        # Remove protocol and domain
        parts = url_or_repo.replace("https://", "").replace("http://", "").split("/")
        # github.com/owner/repo/... -> owner/repo
        if len(parts) >= 3 and parts[0] == "github.com":
            return f"{parts[1]}/{parts[2]}"
    
    return url_or_repo  # Return as-is if we can't parse it
@app.post("/settings/add-module-source", response_class=HTMLResponse)
def add_module_source(
    request: Request,
    source_name: str = Form(...),
    source_repo: str = Form(...)
):
    """Add a new module source"""
    if redirect := require_login(request):
        return redirect
    
    config = load_config()
    sources = config.get("pif_module_sources", [])
    
    # Extract repo from URL if needed (handles both "owner/repo" and "https://github.com/owner/repo/...")
    repo = extract_repo_from_url(source_repo)
    
    # Validate repo format (owner/repo)
    if "/" not in repo or len(repo.split("/")) != 2:
        return RedirectResponse(url="/settings?error=Invalid+repo+format.+Use+owner/repo", status_code=302)
    
    # Check if repo already exists
    if any(s.get("repo") == repo for s in sources):
        return RedirectResponse(url="/settings?error=Repository+already+exists", status_code=302)
    
    new_source = {
        "name": source_name,
        "repo": repo,
        "enabled": True,
        "is_default": False
    }
    sources.append(new_source)
    config["pif_module_sources"] = sources
    save_config(config)
    
    # Clear cache to fetch from new source
    clear_github_api_cache()
    
    log(f"Added module source: {source_name} ({repo})", None, "CONFIG")
    return RedirectResponse(url="/settings", status_code=302)
@app.post("/settings/delete-module-source", response_class=HTMLResponse)
def delete_module_source(request: Request, repo: str = Form(...)):
    """Delete a module source"""
    if redirect := require_login(request):
        return redirect
    
    config = load_config()
    sources = config.get("pif_module_sources", [])
    
    # Find and remove the source
    sources = [s for s in sources if s.get("repo") != repo]
    config["pif_module_sources"] = sources
    save_config(config)
    
    # Clear cache
    clear_github_api_cache()
    
    log(f"Deleted module source: {repo}", None, "CONFIG")
    return RedirectResponse(url="/settings", status_code=302)
@app.post("/settings/toggle-module-source", response_class=HTMLResponse)
def toggle_module_source(request: Request, repo: str = Form(...), enabled: str = Form(...)):
    """Toggle a module source enabled/disabled"""
    if redirect := require_login(request):
        return redirect
    
    config = load_config()
    sources = config.get("pif_module_sources", [])
    
    for source in sources:
        if source.get("repo") == repo:
            source["enabled"] = enabled == "true"
            break
    
    config["pif_module_sources"] = sources
    save_config(config)
    
    # Clear cache
    clear_github_api_cache()
    
    log(f"Toggled module source {repo}: {enabled}", None, "CONFIG")
    return RedirectResponse(url="/settings", status_code=302)
@app.get("/api/pogo-sources")
def get_pogo_sources(request: Request):
    """Get all configured PoGO sources"""
    if not is_logged_in(request):
        return {"error": "Not authenticated"}
    
    config = load_config()
    sources = config.get("pogo_sources", [])
    return {"sources": sources}
@app.post("/settings/add-pogo-source", response_class=HTMLResponse)
def add_pogo_source(
    request: Request,
    source_name: str = Form(...),
    source_type: str = Form(...),
    source_url: str = Form(""),
    source_repo: str = Form("")
):
    """Add a new PoGO source"""
    if redirect := require_login(request):
        return redirect
    
    config = load_config()
    sources = config.get("pogo_sources", [])
    
    # Validate based on type
    if source_type == "mirror":
        if not source_url:
            return RedirectResponse(url="/settings?error=URL+required+for+mirror", status_code=302)
        # Check if URL already exists
        if any(s.get("url") == source_url and s.get("type") == "mirror" for s in sources):
            return RedirectResponse(url="/settings?error=Mirror+URL+already+exists", status_code=302)
        repo = None
    elif source_type == "github":
        # Extract repo from URL if needed (handles both "owner/repo" and "https://github.com/owner/repo/...")
        repo = extract_repo_from_url(source_repo)
        if not repo or "/" not in repo or len(repo.split("/")) != 2:
            return RedirectResponse(url="/settings?error=Invalid+repo+format.+Use+owner/repo", status_code=302)
        # Check if repo already exists
        if any(s.get("repo") == repo for s in sources):
            return RedirectResponse(url="/settings?error=Repository+already+exists", status_code=302)
    else:
        return RedirectResponse(url="/settings?error=Invalid+source+type", status_code=302)
    
    new_source = {
        "name": source_name,
        "type": source_type,
        "enabled": True,
        "is_default": False
    }
    
    if source_type == "mirror":
        new_source["url"] = source_url
    elif source_type == "github":
        new_source["repo"] = repo
    
    sources.append(new_source)
    config["pogo_sources"] = sources
    save_config(config)
    
    # Clear cache to fetch from new source
    get_available_versions.cache_clear()
    
    log(f"Added PoGO source: {source_name} ({source_type})", None, "CONFIG")
    return RedirectResponse(url="/settings", status_code=302)
@app.post("/settings/delete-pogo-source", response_class=HTMLResponse)
def delete_pogo_source(request: Request, source_name: str = Form(...)):
    """Delete a PoGO source"""
    if redirect := require_login(request):
        return redirect
    
    config = load_config()
    sources = config.get("pogo_sources", [])
    
    # Find and remove the source by name
    sources = [s for s in sources if s.get("name") != source_name]
    config["pogo_sources"] = sources
    save_config(config)
    
    # Clear cache
    get_available_versions.cache_clear()
    
    log(f"Deleted PoGO source: {source_name}", None, "CONFIG")
    return RedirectResponse(url="/settings", status_code=302)
@app.post("/settings/toggle-pogo-source", response_class=HTMLResponse)
def toggle_pogo_source(request: Request, source_name: str = Form(...), enabled: str = Form(...)):
    """Toggle a PoGO source enabled/disabled"""
    if redirect := require_login(request):
        return redirect
    
    config = load_config()
    sources = config.get("pogo_sources", [])
    
    for source in sources:
        if source.get("name") == source_name:
            source["enabled"] = enabled == "true"
            break
    
    config["pogo_sources"] = sources
    save_config(config)
    
    # Clear cache
    get_available_versions.cache_clear()
    
    log(f"Toggled PoGO source {source_name}: {enabled}", None, "CONFIG")
    return RedirectResponse(url="/settings", status_code=302)
@app.get("/update-status")
def get_update_status():
    return {
        "status": state.update_in_progress,
        "progress": state.current_progress,
        "message": "Installation in progress..." if state.update_in_progress else "Idle"
    }
@app.get("/api/status")
async def api_status(request: Request, apk_type: str = "google"):
    if not is_logged_in(request):
        return {"error": "Not authenticated"}
    
    # Validate apk_type parameter
    if apk_type not in ("google", "samsung"):
        apk_type = "google"
    
    log(f"API /status requested with apk_type={apk_type}", None, "DEBUG")
    status_data = await get_status_data_with_tailwind_classes(apk_type)
    return status_data
@app.get("/api/pogo-versions")
async def api_pogo_versions(request: Request):
    """Returns ALL available PoGO versions (Google and Samsung) for dropdown"""
    if not is_logged_in(request):
        return {"error": "Not authenticated"}

    google_versions = get_available_local_google_versions()
    samsung_versions = get_available_samsung_versions()

    # Combine and sort all versions
    all_versions = []
    all_versions.extend(google_versions)
    all_versions.extend(samsung_versions)

    sorted_versions = sorted(
        all_versions,
        key=lambda x: [int(n) for n in x["version"].split(".")],
        reverse=True
    )

    return {
        "versions": sorted_versions,
        "latest": get_available_local_versions("all").get("latest", {}),
        "previous": get_available_local_versions("all").get("previous", {})
    }
@app.get("/api/mitm-versions")
async def api_mitm_versions(request: Request):
    """Returns available MITM (MapWorld) versions for dropdown"""
    if not is_logged_in(request):
        return {"error": "Not authenticated"}

    mitm_versions = get_available_mitm_versions()

    return {
        "versions": mitm_versions
    }
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
        
        log("Restarting apps", device_id, "MONITOR")
        success = await optimized_app_start(device_id, control_enabled)
        
        if success:
            return RedirectResponse(url="/status?success=Apps restarted successfully", status_code=302)
        else:
            return RedirectResponse(url="/status?error=Failed to restart apps", status_code=302)
    except Exception as e:
        log(f"Error restarting apps: {str(e)}", device_id, "ERROR")
        return RedirectResponse(url="/status?error=Failed to restart apps", status_code=302)
@app.post("/devices/reboot", response_class=HTMLResponse)
def reboot_device(request: Request, device_ip: str = Form(...)):
    if redirect := require_login(request):
        return redirect
    
    try:
        device_id = format_device_ip = format_device_id(device_ip)
        
        device_details = get_device_details(device_id)
        display_name = device_details.get("display_name", device_id.split(":")[0] if ":" in device_id else device_id)
        
        log("Rebooting device", device_id, "MONITOR")
        
        adb_pool.execute_command(device_id, ["adb", "reboot"])
        
        return RedirectResponse(url="/status?success=Reboot command sent", status_code=302)
    except Exception as e:
        log(f"Error rebooting device: {str(e)}", device_id, "ERROR")
        return RedirectResponse(url="/status?error=Failed to reboot device", status_code=302)
@app.websocket("/ws/htmx/status")
async def websocket_htmx_endpoint(websocket: WebSocket):
    """WebSocket endpoint for HTMX streaming updates"""
    await ws_manager.connect(websocket)
    try:
        status_data = await get_status_data()
        html = templates.env.get_template("partials/device_table.html").render(
            devices=status_data["devices"]
        )
        await websocket.send_text(html)

        while True:
            try:
                data = await websocket.receive_text()

                if data == "refresh":
                    status_data = await get_status_data()
                    html = templates.env.get_template("partials/device_table.html").render(
                        devices=status_data["devices"]
                    )
                    await websocket.send_text(html)
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
            <div class="w-{state.current_progress}% shadow-none flex flex-col text-center whitespace-nowrap text-white justify-center bg-blue-500 transition-all duration-500"></div>
        </div>
        <p class="text-center text-sm text-gray-300">
            {state.current_progress}% Complete
        </p>
    </div>
    """
    return HTMLResponse(content=progress_html)
