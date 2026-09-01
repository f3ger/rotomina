"""Discord webhooks, notifications and bot"""
import asyncio
import datetime
import requests
import time

from . import state
from .config import APK_DIR, EXTRACT_DIR, load_config, save_config
from .utils import log

DISCORD_BOT_AVAILABLE = True
DISCORD_IMPORT_ERROR: str = ""
DISCORD_COLOR_RED = 0xE74C3C     # Error/Offline
DISCORD_COLOR_GREEN = 0x2ECC71   # Success/Online
DISCORD_COLOR_BLUE = 0x3498DB    # Info/Update
DISCORD_COLOR_ORANGE = 0xE67E22  # Warning/Restart
try:
    import discord
    from discord import app_commands
except ImportError as _discord_err:
    DISCORD_BOT_AVAILABLE = False
    DISCORD_IMPORT_ERROR = str(_discord_err)
async def send_discord_webhook(message: str, title: str = None, color: int = DISCORD_COLOR_BLUE):
    """Sends a notification via Discord webhook URL."""
    cfg = load_config()
    webhook_url = cfg.get("discord_webhook_url", "").strip()
    if not webhook_url:
        return False
    try:
        embed = {
            "title": title or "Rotomina Notification",
            "description": message,
            "color": color,
            "timestamp": datetime.datetime.now(datetime.timezone.utc).isoformat(),
            "footer": {"text": "Rotomina"}
        }
        payload = {"embeds": [embed]}
        response = requests.post(webhook_url, json=payload, timeout=10)
        if response.status_code in (200, 204):
            log(f"Discord webhook sent: {message}", None, "API")
            return True
        else:
            log(f"Discord webhook error: HTTP {response.status_code}", None, "ERROR")
            return False
    except Exception as e:
        log(f"Discord webhook error: {e}", None, "ERROR")
        return False
async def send_discord_notification(message: str, title: str = None, color: int = DISCORD_COLOR_BLUE):
    """Sends a notification via Discord webhook (if configured) or bot."""
    cfg = load_config()
    # Try webhook first if configured
    webhook_url = cfg.get("discord_webhook_url", "").strip()
    if webhook_url:
        return await send_discord_webhook(message, title, color)
    # Fallback to bot if available
    if not DISCORD_BOT_AVAILABLE or state._discord_bot_client is None:
        return False
    channel_id = cfg.get("discord_bot_notify_channel_id", "").strip()
    if not channel_id:
        return False
    try:
        channel = state._discord_bot_client.get_channel(int(channel_id))
        if channel is None:
            log(f"Discord notify channel {channel_id} not found", None, "ERROR")
            return False
        embed = discord.Embed(
            title=title or "Rotomina Notification",
            description=message,
            color=color,
            timestamp=datetime.datetime.now(datetime.timezone.utc),
        )
        embed.set_footer(text="Rotomina")
        await channel.send(embed=embed)
        log(f"Discord notification sent: {message}", None, "API")
        return True
    except Exception as e:
        log(f"Discord notification error: {e}", None, "ERROR")
        return False
_discord_status_message_id: "int | None" = None
_discord_recent_events: list = []  # List of (timestamp, message) tuples, max 10
def add_discord_event(message: str):
    """Add an event to the recent events list for the live status embed."""
    _discord_recent_events.insert(0, (time.time(), message))
    del _discord_recent_events[10:]  # Keep last 10
def _format_relative_time(ts: float) -> str:
    """Format a timestamp as relative time (e.g. '2 min ago')."""
    diff = int(time.time() - ts)
    if diff < 60:
        return "just now"
    elif diff < 3600:
        m = diff // 60
        return f"{m} min ago"
    elif diff < 86400:
        h = diff // 3600
        return f"{h}h ago"
    else:
        d = diff // 86400
        return f"{d}d ago"
async def start_discord_bot():
    from .update import get_available_versions, download_apk, unzip_apk, perform_installations, optimized_app_start
    """Start the Discord bot if a token is configured. Runs as a background task."""

    if not DISCORD_BOT_AVAILABLE:
        log("discord.py not installed – bot disabled. Run: pip install discord.py>=2.3.0", None, "DISCORD")
        return

    config = load_config()
    token = config.get("discord_bot_token", "").strip()
    if not token:
        return

    intents = discord.Intents.default()
    client = discord.Client(intents=intents)
    tree = app_commands.CommandTree(client)
    state._discord_bot_client = client

    def _check_permissions(interaction: discord.Interaction) -> bool:
        """Returns True if the interaction satisfies the configured channel/role restrictions."""
        cfg = load_config()
        allowed_channel = cfg.get("discord_bot_channel_id", "").strip()
        allowed_role = cfg.get("discord_bot_role_id", "").strip()
        if allowed_channel and str(interaction.channel_id) != allowed_channel:
            return False
        if allowed_role:
            role_ids = [str(r.id) for r in getattr(interaction.user, "roles", [])]
            if allowed_role not in role_ids:
                return False
        return True

    @tree.command(name="update_pogo", description="Update PoGo on all devices")
    async def _cmd_update_pogo(interaction: discord.Interaction):
        if not _check_permissions(interaction):
            await interaction.response.send_message("Not authorized.", ephemeral=True)
            return
        if state.update_in_progress:
            await interaction.response.send_message("An update is already in progress.", ephemeral=True)
            return
        await interaction.response.send_message("⏳ Starting PoGo update…")

        async def _run():
            try:
                cfg = load_config()
                device_ips = [d["ip"] for d in cfg.get("devices", [])]
                versions = get_available_versions()
                if not versions:
                    await interaction.followup.send("❌ Error: No versions available.")
                    return
                entry = versions["latest"]
                apk_file = APK_DIR / entry["filename"]
                if not apk_file.exists():
                    apk_file = download_apk(entry)
                extract_dir = EXTRACT_DIR / entry["version"]
                unzip_apk(apk_file, extract_dir)
                await perform_installations(device_ips, extract_dir)
                await interaction.followup.send(
                    f"✅ PoGo {entry['version']} installed on {len(device_ips)} device(s)."
                )
            except Exception as e:
                await interaction.followup.send(f"❌ Update failed: {e}")

        asyncio.create_task(_run())

    @tree.command(name="restart", description="Restart PoGo/MITM on all devices")
    async def _cmd_restart(interaction: discord.Interaction):
        if not _check_permissions(interaction):
            await interaction.response.send_message("Not authorized.", ephemeral=True)
            return
        await interaction.response.send_message("⏳ Initiating restart…")

        async def _run():
            try:
                cfg = load_config()
                devices = cfg.get("devices", [])
                for dev in devices:
                    ip = dev["ip"]
                    control_enabled = dev.get("control_enabled", False)
                    await optimized_app_start(ip, control_enabled)
                await interaction.followup.send(f"✅ Restart triggered on {len(devices)} device(s).")
            except Exception as e:
                await interaction.followup.send(f"❌ Restart failed: {e}")

        asyncio.create_task(_run())

    @client.event
    async def on_ready():
        await tree.sync()
        log(f"Discord Bot logged in as {client.user}", None, "DISCORD")
        await update_discord_status_embed()

    try:
        await client.start(token)
    except discord.LoginFailure:
        log("Discord Bot: Invalid token – bot not started.", None, "DISCORD")
    except Exception as e:
        log(f"Discord Bot error: {e}", None, "DISCORD")
    finally:
        try:
            await client.close()
        except Exception:
            pass
        # Clear global reference when bot disconnects
        if state._discord_bot_client is client:
            state._discord_bot_client = None
async def update_discord_status_embed():
    from .update import get_status_data
    """Update or create the persistent status embed in the notification channel."""
    global _discord_status_message_id
    if not DISCORD_BOT_AVAILABLE or state._discord_bot_client is None:
        return
    if not state._discord_bot_client.is_ready():
        return

    cfg = load_config()
    channel_id = cfg.get("discord_bot_notify_channel_id", "").strip()
    if not channel_id:
        return

    try:
        channel = state._discord_bot_client.get_channel(int(channel_id))
        if channel is None:
            return

        # Build embed
        data = await get_status_data()
        devices = data.get("devices", [])
        online = sum(1 for d in devices if d.get("is_alive"))
        total = len(devices)

        if online == total:
            color = DISCORD_COLOR_GREEN
        elif online == 0:
            color = DISCORD_COLOR_RED
        else:
            color = DISCORD_COLOR_ORANGE

        summary_icon = "✅" if online == total else ("🔴" if online == 0 else "⚠️")
        lines = [f"**{summary_icon} {online}/{total} Devices Online**\n"]

        for dev in devices:
            alive = "🟢" if dev.get("is_alive") else "🔴"
            adb = "✅" if dev.get("status") else "❌"
            in_upd = " ⏳" if dev.get("in_update") else ""
            name = dev.get("display_name") or dev.get("ip", "?")
            pogo_ver = dev.get("pogo", "N/A")
            mitm_ver = dev.get("mitm", "N/A")
            lines.append(f"{alive} **{name}**{in_upd}")
            lines.append(f"ADB {adb} · PoGo `{pogo_ver}` · MITM `{mitm_ver}`\n")

        # Recent events section
        if _discord_recent_events:
            lines.append("📋 **Recent Events**")
            for ts, event_msg in _discord_recent_events[:10]:
                rel = _format_relative_time(ts)
                lines.append(f"• {event_msg} ({rel})")

        embed = discord.Embed(
            title="Rotomina – Device Status",
            description="\n".join(lines),
            color=color,
            timestamp=datetime.datetime.now(datetime.timezone.utc),
        )
        embed.set_footer(text="Rotomina · Live Status")

        # Try to edit existing message
        msg_id = _discord_status_message_id or cfg.get("discord_status_message_id")
        if msg_id:
            try:
                msg = await channel.fetch_message(int(msg_id))
                await msg.edit(embed=embed)
                return
            except (discord.NotFound, discord.HTTPException):
                pass  # Message deleted → send new one

        # Send new message and persist ID
        msg = await channel.send(embed=embed)
        _discord_status_message_id = msg.id
        cfg["discord_status_message_id"] = msg.id
        save_config(cfg)
    except Exception as e:
        log(f"Discord status embed error: {e}", None, "ERROR")
async def notify_device_offline(device_name: str, ip: str):
    add_discord_event(f"{device_name} went offline")
    await update_discord_status_embed()
    await send_discord_webhook(f"Device {device_name} ({ip}) went offline", "Device Offline", DISCORD_COLOR_RED)
async def notify_device_online(device_name: str, ip: str):
    add_discord_event(f"{device_name} is back online")
    await update_discord_status_embed()
    await send_discord_webhook(f"Device {device_name} ({ip}) is back online", "Device Online", DISCORD_COLOR_GREEN)
async def notify_memory_restart(device_name: str, ip: str, memory: int, threshold: int):
    add_discord_event(f"{device_name} restarted — low memory")
    await update_discord_status_embed()
    await send_discord_webhook(f"Device {device_name} restarted due to low memory ({memory}MB < {threshold}MB)", "Memory Restart", DISCORD_COLOR_ORANGE)
async def notify_update_installed(device_name: str, ip: str, update_type: str, version: str):
    add_discord_event(f"{update_type} {version} installed on {device_name}")
    await update_discord_status_embed()
    await send_discord_webhook(f"{update_type} {version} installed on {device_name}", "Update Installed", DISCORD_COLOR_GREEN)
async def notify_update_downloaded(update_type: str, version: str):
    add_discord_event(f"{update_type} {version} downloaded")
    await update_discord_status_embed()
    await send_discord_webhook(f"{update_type} {version} downloaded and ready for installation", "Update Downloaded", DISCORD_COLOR_BLUE)
async def notify_invalid_token(device_name: str, device_ip: str, error_message: str):
    """Sends Discord notification when device token is invalid"""
    add_discord_event(f"Token invalid for {device_name}")
    await update_discord_status_embed()
    await send_discord_webhook(f"Invalid token for {device_name} ({device_ip}): {error_message}", "Invalid Token", DISCORD_COLOR_RED)
