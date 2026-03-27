import flet as ft
import requests
from zeroconf import Zeroconf, ServiceBrowser
import threading
import uuid
import json
import os
import time
import subprocess
import io
import socket
import zipfile
from queue import Queue
import psutil
import platform
from datetime import datetime

import glob

# Read version from @version.txt sitting next to the script/exe.
# sys.frozen is True when running as a PyInstaller exe — use exe's folder.
# Falls back to hardcoded string if file not found.
import sys as _sys
_VERSION_DIR = os.path.dirname(_sys.executable if getattr(_sys, 'frozen', False) else os.path.abspath(__file__))
_VERSION_FILE = os.path.join(_VERSION_DIR, "@version.txt")
try:
    with open(_VERSION_FILE, "r") as _vf:
        APP_VERSION = _vf.read().strip()
except:
    APP_VERSION = "4.5.0"  # fallback if version file missing
CACHE_FILE = "wledcc_cache.json"
CACHE_BACKUP_MAX = 10  # keep this many backup files
LOG_MAX = 10  # keep this many session log files
# Save all user data to AppData\Roaming\WLEDCC so the app works correctly
# when installed in Program Files (which is write-protected for normal users).
LOG_DIR = os.path.join(os.environ.get("APPDATA", os.path.dirname(os.path.abspath(__file__))), "WLEDCC")
os.makedirs(LOG_DIR, exist_ok=True)  # create folder on first run if it doesn't exist
CACHE_FILE = os.path.join(LOG_DIR, "wledcc_cache.json")
GITHUB_RELEASES_URL = "https://api.github.com/repos/Aircoookie/WLED/releases/latest"
LEDFX_RELEASES_URL = "https://api.github.com/repos/LedFx/LedFx/releases/latest"
MAGIC_HOME_PORT = 5577
MAGIC_HOME_DISCOVERY_PORT = 48899

# Unified polling configuration for optimal ESP32 performance
WLED_BASE_INTERVAL = 5.0    # Base seconds between WLED poll rounds
WLED_SCALE_FACTOR = 2.0     # Additional seconds per 10 devices
WLED_MAX_INTERVAL = 15.0    # Maximum polling interval (cap)
LEDFX_POLL_INTERVAL = 3.0    # Fixed LedFx API poll interval
UNFOCUSED_PAUSE = 5.0       # Polling pause when app window not focused

class WLEDApp:
    def __init__(self, page: ft.Page):
        self.page = page
        self.devices = {}  
        self.device_types = {} 
        self.effect_maps = {} 
        self.cards = {}    
        self.fail_counts = {} 
        self.locks = {} 
        self.is_focused = True 
        self.running = True  
        # --- Slider drag smoothing ---
        self._dragging = set()
        self._pending_bri = {}
        self._last_slider_ui = {}
        self._last_defer_log = {}
        self.is_refreshing = False
        self.latest_release_ver = None
        self.ledfx_latest_ver = None
        self.ledfx_current_ver = "2.0.0" 
        self.brightness_queue = Queue()
        self.rainbow_hue = 0  # shared hue position for all ON-card animations
        # Title animation settings
        self.title_effect = "rainbow_wave"  # rainbow_wave, color_loop, breathing, strobe, solid
        self.title_speed  = 4.0             # hue step per tick
        self.title_color  = "#ff0000"       # base color for non-rainbow effects
        # Border animation settings
        self.border_effect = "color_loop"   # rainbow_wave, color_loop, breathing, strobe, solid
        self.border_speed  = 4.0
        self.border_color  = "#ff0000"
        # Internal animation state
        self._breath_title = 0.0
        self._breath_title_dir = 1
        self._breath_border = 0.0
        self._breath_border_dir = 1
        self._strobe_title = True
        self._strobe_border = True
        self.brightness_debounce_timer = None
        self.current_master_bri = 128
        self.prev_master_bri = 128
        self.individual_brightness = {}
        self.custom_names = {}  # ip -> user-defined display name
        self.display_names = {}  # ip -> last known display name shown on card
        self.preset_cache = {}   # ip -> {id: name} dict of presets
        self.active_preset = {}  # ip -> currently active preset ID (-1 = none/effect only)
        self.scenes = [None, None, None, None]  # 4 scene slots, each None or {name, data}
        self.card_order = []  # ordered list of IPs matching last saved visual order
        self.device_macs = {}    # ip -> mac_suffix (last 6 chars of MAC)
        self.custom_devices = {}  # key -> {name, url, is_local} for non-WLED/MH devices
        self.mac_to_ip = {}      # mac_suffix -> current ip
        self.card_ids = {}        # ip -> stable UUID for this card
        self.card_id_to_ip = {}   # UUID -> current ip (updated on IP change)
        self.merge_mode = False   # True while user is in merge mode
        self.debug_mode = False   # True = show verbose debug logs
        self.debug_on_open = False   # True = enable debug mode when log panel opens
        self.log_auto_open = False   # True = log panel opens automatically at startup
        # --- Log de-dup + change tracking ---
        self._last_log_by_key = {}
        self._last_ping_state = {}
        self._last_ledfx_state = {}
        self.draggable_map = {}   # flet control uid -> ip, for drag resolution
        self.scene_btn_refs = {}  # idx -> Container ref for rainbow border on active scene
        self.active_scene_idx = None  # which scene is currently active (glowing)
        self.ledfx_running = False  # mirrors ledfx_monitor_loop — used to skip polls
        self._ledfx_launching = False  # True while launch sequence is running
        self.ledfx_virtual_map = {}  # vid -> ip
        self.ledfx_ip_to_virtual = {}  # ip -> vid (reverse map for badge click)
        self.ledfx_segment_vids = {}  # ip -> [segment_vid, ...] for segment virtual deactivation
        self._releasing_ips = set()  # IPs currently being released — poll loop skips re-locking
        self._ledfx_ip_cache = {}    # mDNS hostname -> resolved IP
        self._ledfx_resolve_fails = {}  # hostname -> fail count (suppress after 3)
        self.live_ips = set()     # IPs currently in LedFx live mode — heartbeat paused
        self.lor2_ips = set()     # IPs where we sent lor:2 (WLED holding control)
        self._scene_mode = "wled"   # "wled" or "ledfx" — which scene set is showing
        self.ledfx_scenes = {}      # id -> name, fetched from LedFx on start
        self.mh_mode = {}         # ip -> {"pattern": byte or None} — None means static
        self.mh_last_rgb = {}     # ip -> (r, g, b) last color sent
        self.mh_last_cmd = {}     # ip -> timestamp of last command sent (rate limiter)
        self.ledfx_path = None
        
        # --- mDNS ---
        self.browser = None
        self.zeroconf = None
        self.browser = None

        # Unified polling system — track devices by control mode
        self.wled_devices = set()    # IPs controlled by WLED (not in live mode)
        self.ledfx_devices = set()   # IPs controlled by LedFx (in live mode)
        self.poll_counters = {}      # ip -> consecutive poll count for adaptive backoff

        # Open rotating session log file
        self._log_fh = self._open_session_log()
        self.file_picker = ft.FilePicker(on_result=self.on_file_result)
        self.page.overlay.append(self.file_picker)

        self.load_cache()
        self.setup_ui()
        
        # Apply startup preferences: if auto-open is on, log_container was set visible
        # in setup_ui already. If debug_on_open is also on, activate debug mode now.
        if self.log_auto_open and self.debug_on_open:
            self.debug_mode = True
            self._debug_btn_text.value = "DEBUG: ON"
            self._debug_btn_text.color = "orange400"

        self.log(f"System initialized. Version {APP_VERSION}", color="white")
        self.log(f"[Version] Reading from: {_VERSION_FILE}", color="grey500")
        if getattr(self, "_cache_load_warning", None):
            self.log(self._cache_load_warning, color="red400")
        threading.Thread(target=self.fetch_latest_release, daemon=True).start()
        threading.Thread(target=self.check_ledfx_updates, daemon=True).start()
        threading.Thread(target=self.brightness_worker, daemon=True).start()
        threading.Thread(target=self.rainbow_loop, daemon=True).start()
        threading.Thread(target=self.ledfx_monitor_loop, daemon=True).start()
        threading.Thread(target=self.unified_poll_loop, daemon=True).start()
        # Run one startup scan after a short delay — gives UI time to settle
        def _delayed_startup_scan():
            
            if self.cards:
                return   # skip auto-scan if devices already exist
            time.sleep(5)
            # Update button to show scanning state
            self._refresh_icon.color = "cyan"
            self._refresh_text.value = "SCANNING..."
            self._refresh_text.color = "cyan"
            self.refresh_btn.disabled = True
            try: self.refresh_btn.update()
            except: pass
            self.rescan_devices()
            # Poll loop handles live state — nothing needed here
        threading.Thread(target=_delayed_startup_scan, daemon=True).start()
        self.page.on_close = self.cleanup

    def _open_session_log(self):
        """Open a new session log file, rotating old ones if needed."""
        try:
            # Rotate — delete oldest if we have LOG_MAX already
            pattern = os.path.join(LOG_DIR, "wled_session_*.log")
            existing = sorted(glob.glob(pattern))
            while len(existing) >= LOG_MAX:
                os.remove(existing.pop(0))
            ts = datetime.now().strftime("%Y%m%d_%H%M%S")
            path = os.path.join(LOG_DIR, f"wled_session_{ts}.log")
            fh = open(path, "w", encoding="utf-8", buffering=1)
            fh.write(f"=== WLED App Session {ts} ===\n")
            return fh
        except Exception as e:
            return None

    def log(self, message, color="grey300"):
        timestamp = datetime.now().strftime("%H:%M:%S")
        self.log_lines.controls.append(
            ft.Text(f"[{timestamp}] {message}", size=11, color=color, selectable=True)
        )
        # Trim oldest entries to keep UI responsive — file log keeps full history
        if len(self.log_lines.controls) > 500:
            del self.log_lines.controls[:100]  # drop oldest 100 at a time
        # Write to session log file
        if self._log_fh:
            try: self._log_fh.write(f"[{timestamp}] {message}\n")
            except: pass
        if not self.running: return
        try:
            self.log_lines.update()
            if self.log_autoscroll:
                self.log_lines.scroll_to(offset=-1, duration=50)
        except: pass

    def toggle_autoscroll(self, e):
        self.log_autoscroll = not self.log_autoscroll
        label = "AUTO-SCROLL: ON" if self.log_autoscroll else "AUTO-SCROLL: OFF"
        color = "cyan" if self.log_autoscroll else "grey600"
        self.autoscroll_btn.content.value = label
        self.autoscroll_btn.content.color = color
        try: self.autoscroll_btn.update()
        except: pass

    def clear_log(self, e):
        self.log_lines.controls.clear()
        try: self.log_lines.update()
        except: pass

    def toggle_debug(self, e):
        self.debug_mode = not self.debug_mode
        self._debug_btn_text.value = "DEBUG: ON" if self.debug_mode else "DEBUG: OFF"
        self._debug_btn_text.color = "orange400" if self.debug_mode else "grey400"
        try: self.debug_btn.update()
        except: pass
        self.log(f"[Debug] Debug mode {'ON' if self.debug_mode else 'OFF'}", 
                 color="orange400" if self.debug_mode else "grey400")

    def _on_debug_on_open_change(self, e):
        self.debug_on_open = e.control.value
        self.save_cache()
        self.log(f"[Debug] 'Debug on open' {'enabled' if self.debug_on_open else 'disabled'}", color="grey500")

    def _on_log_auto_open_change(self, e):
        self.log_auto_open = e.control.value
        self.save_cache()
        self.log(f"[Log] 'Auto-open log' at startup {'enabled' if self.log_auto_open else 'disabled'}", color="grey500")

    def dbg(self, message, color="grey500"):
        """Log only when debug mode is on."""
        if self.debug_mode:
            self.log(f"[DBGflat1] {message}", color=color)

    def log_unique(self, key, message, color="grey300"):

        last = self._last_log_by_key.get(key)

        if last == message:

            return False

        self._last_log_by_key[key] = message

        self.log(message, color=color)

        return True


    def dbg_unique(self, key, message, color="grey500"):

        if not self.debug_mode:

            return False

        return self.log_unique(key, f"[DBGflatunique2] {message}", color=color)


    def _mark(self, field, changed, s):

        return s + ("▲" if field in changed else "")


    def _dbg_wled_ping(self, ip, name, is_on, bri, fx, color, rssi, live):

        if not self.debug_mode:

            return

        # build normalized state

        try:

            bri_pct = str(int((int(bri)/255)*100)) + "%" if bri is not None else "?"

        except:

            bri_pct = "?"

        state = {"on": bool(is_on), "bri": bri_pct, "fx": str(fx), "color": str(color), "rssi": (int(rssi) if rssi is not None else None), "live": bool(live)}

        last = self._last_ping_state.get(ip)

        changed = []

        if last is None:

            changed = ["on","bri","fx","color","signal","live"]

        else:

            if last.get("on") != state["on"]: changed.append("on")

            if last.get("bri") != state["bri"]: changed.append("bri")

            if last.get("fx") != state["fx"]: changed.append("fx")

            if last.get("color") != state["color"]: changed.append("color")

            lr, nr = last.get("rssi"), state.get("rssi")

            if lr is None and nr is not None: changed.append("signal")

            elif lr is not None and nr is None: changed.append("signal")

            elif lr is not None and nr is not None and abs(int(nr)-int(lr)) >= 10: changed.append("signal")

            if last.get("live") != state["live"]: changed.append("live")

        if not changed:

            return

        self._last_ping_state[ip] = state

        msg = f"Ping {name} ({ip}): "

        msg += "on=" + self._mark("on", changed, str(state["on"])) + " "

        msg += "bri=" + self._mark("bri", changed, state["bri"]) + " "

        msg += "fx=" + self._mark("fx", changed, state["fx"]) + " "

        msg += "color=" + self._mark("color", changed, state["color"])

        if state["rssi"] is not None:

            msg += " signal=" + self._mark("signal", changed, str(state["rssi"]) + "%")

        msg += " live=" + self._mark("live", changed, str(state["live"]))

        msg += "  Δ " + ",".join(changed)

        self.log_unique(f"ping:{ip}", f"[DBGflatwledUNIQUE1] {msg}", color="white")


    def _dbg_ledfx_poll(self, ip, vid, active, streaming, bri, effect_name):

        if not self.debug_mode:

            return

        state = {"active": bool(active), "streaming": bool(streaming), "bri": str(bri), "effect": str(effect_name)}

        last = self._last_ledfx_state.get(ip)

        changed = []

        if last is None:

            changed = ["active","streaming","bri","effect"]

        else:

            if last.get("active") != state["active"]: changed.append("active")

            if last.get("streaming") != state["streaming"]: changed.append("streaming")

            if last.get("bri") != state["bri"]: changed.append("bri")

            if last.get("effect") != state["effect"]: changed.append("effect")

        if not changed:

            return

        self._last_ledfx_state[ip] = state

        msg = f"LedFx Poll {vid} ({ip}): "

        msg += "active=" + self._mark("active", changed, str(state["active"])) + " "

        msg += "streaming=" + self._mark("streaming", changed, str(state["streaming"])) + " "

        msg += "bri=" + self._mark("bri", changed, state["bri"]) + " "

        msg += "effect=" + self._mark("effect", changed, state["effect"])

        msg += "  Δ " + ",".join(changed)

        self.log_unique(f"ledfx:{ip}", f"[DBGflatledfxunique1] {msg}", color="white")


    def copy_log(self, e):
        lines = [c.value for c in self.log_lines.controls if hasattr(c, "value")]
        self.page.set_clipboard("\n".join(lines))
        self.copy_log_btn.content.value = "COPIED!"
        self.copy_log_btn.content.color = "cyan"
        try: self.copy_log_btn.update()
        except: pass
        def _reset():
            import time; time.sleep(1.5)
            self.copy_log_btn.content.value = "COPY LOG"
            self.copy_log_btn.content.color = "grey400"
            try: self.copy_log_btn.update()
            except: pass
        threading.Thread(target=_reset, daemon=True).start()

    def toggle_logs(self, e):
        new_vis = not self.log_container.visible
        self.log_container.visible = new_vis
        if new_vis and self.debug_on_open and not self.debug_mode:
            self.debug_mode = True
            self._debug_btn_text.value = "DEBUG: ON"
            self._debug_btn_text.color = "orange400"
        self.page.update()

    def open_log_folder(self, e):
        """Open the data folder in Windows Explorer so users can find logs and cache."""
        try:
            os.startfile(LOG_DIR)
        except Exception as ex:
            self.log(f"[Log] Could not open folder: {ex}", color="red400")

    def _open_log(self):
        """Force the log panel open and scroll to bottom."""
        if not self.log_container.visible:
            self.log_container.visible = True
            if self.debug_on_open and not self.debug_mode:
                self.debug_mode = True
                self._debug_btn_text.value = "DEBUG: ON"
                self._debug_btn_text.color = "orange400"
            try: self.page.update()
            except: pass

    def show_help(self, e):
        self.help_dialog.open = True
        self.page.update()

    def is_ledfx_running(self):
        for proc in psutil.process_iter(['name']):
            try:
                if proc.info['name'] and proc.info['name'].lower() == "ledfx.exe":
                    return True
            except (psutil.NoSuchProcess, psutil.AccessDenied): continue
        return False

    def ledfx_monitor_loop(self):
        _was_running = False
        _first_check = True
        time.sleep(8)  # wait for cards to load before first live check
        while self.running:
            is_running = self.is_ledfx_running()
            self.ledfx_running = is_running

            # On first check, if LedFx is already running treat it as a fresh start
            if _first_check and is_running:
                _was_running = False
            _first_check = False
            _txt = "STOP LEDFX" if is_running else "START LEDFX"
            _bg  = "red800"   if is_running else "purple700"
            if not self._ledfx_launching:  # dont overwrite STARTING... text
                for _b in self._ledfx_btns:
                    _b.text = _txt; _b.bgcolor = _bg
                for _u in self._ledfx_ui_btns:
                    _u.visible = is_running
                for _t in self._scene_toggle_btns:
                    _t.visible = is_running
                if self.running:
                    for _b in self._ledfx_btns:
                        try: _b.update()
                        except: pass
                    for _u in self._ledfx_ui_btns:
                        try: _u.update()
                        except: pass
                    for _t in self._scene_toggle_btns:
                        try: _t.update()
                        except: pass
            # LedFx just started — show grey badge on all WLED cards immediately,
            # fetch LedFx scenes for the scene toggle
            if is_running and not _was_running:
                self.log("[Live] LedFx started — showing badges on all WLED devices", color="cyan")
                for ip, c in list(self.cards.items()):
                    if c.get("_is_custom") or self.device_types.get(ip) != "wled": continue
                    if ip in self.live_ips: continue  # already orange
                    c["live_badge"].visible = True
                    c["live_icon"].color = "grey500"
                    c["live_text"].color = "grey500"
                    c["live_badge"].bgcolor = "#1e1e2a"
                    c["live_badge"].border = ft.border.all(1, "grey700")
                    c["live_badge"].tooltip = "Click to re-activate in LedFx"
                    try: c["live_badge"].update()
                    except: pass
                def _delayed_scene_fetch():
                    time.sleep(3)
                    self.toggle_scene_mode()
                    
                threading.Thread(target=_delayed_scene_fetch, daemon=True).start()
            # LedFx just stopped — revert to WLED scenes, hide all badges
            if _was_running and not is_running:
                self._scene_mode = "wled"
                self.ledfx_scenes = {}
                self._rebuild_scene_rows_for_mode()
                for _t in self._scene_toggle_btns:
                    _t.text = "LEDFX SCENES"
                    try: _t.update()
                    except: pass
            # LedFx just stopped — hide all badges and wait for devices to release
            if _was_running and not is_running:
                self.log("[Live] LedFx stopped — waiting 5s then confirming release via WLED...", color="cyan")
                self._ledfx_ip_cache.clear()
                self.ledfx_virtual_map.clear()
                self.ledfx_ip_to_virtual.clear()
                self.ledfx_segment_vids.clear()
                self._releasing_ips.clear()
                self._ledfx_resolve_fails.clear()
                # Hide all badges — both orange (live) and grey (inactive) — LedFx is gone
                for ip, c in list(self.cards.items()):
                    if c.get("_is_custom"): continue
                    if c.get("live_badge") and c["live_badge"].visible:
                        c["live_badge"].visible = False
                        try: c["live_badge"].update()
                        except: pass
                def _confirm_release():
                    time.sleep(5)
                    locked_ips = list(self.live_ips)
                    self.log(f"[Live] Checking {len(locked_ips)} locked devices for release...", color="cyan")
                    for ip in locked_ips:
                        if not self.running: break
                        try:
                            r = requests.get(f"http://{ip}/json", timeout=2.0).json()
                            still_live = r.get("state", {}).get("live", False)
                            if not still_live:
                                self.page.run_task(self._async_confirm_release, ip)
                            else:
                                self.dbg(f"{ip} still live=True after LedFx stop — leaving locked")
                        except Exception as e:
                            self.dbg(f"{ip} ping failed during release confirm: {e}")
                            # Ping failed — unlock anyway, heartbeat will correct
                            self.page.run_task(self._async_confirm_release, ip)
                    # Reset fail counts and resume heartbeat
                    for ip in list(self.cards.keys()):
                        self.fail_counts[ip] = 0
                    self.log("[Live] Heartbeat resumed for all devices", color="green400")
                threading.Thread(target=_confirm_release, daemon=True).start()
            _was_running = is_running
            time.sleep(2)

    def _resolve_ledfx_ip(self, hostname):
        """Resolve mDNS hostname to IP, with cache. Returns None if resolution fails."""
        if not hostname: return None
        # Already an IP address — return as-is
        import re as _re
        if _re.match(r'^\d+\.\d+\.\d+\.\d+$', hostname):
            return hostname
        if hostname in self._ledfx_ip_cache:
            return self._ledfx_ip_cache[hostname]
        try:
            import socket as _socket
            ip = _socket.gethostbyname(hostname)
            self._ledfx_ip_cache[hostname] = ip
            self._ledfx_resolve_fails.pop(hostname, None)  # clear fail count on success
            self.log(f"[LedFx Poll] Resolved {hostname} → {ip}", color="grey500")
            return ip
        except Exception as e:
            count = self._ledfx_resolve_fails.get(hostname, 0) + 1
            self._ledfx_resolve_fails[hostname] = count
            if count <= 3:
                self.log(f"[LedFx Poll] Failed to resolve '{hostname}': {e}", color="orange400")
            # silently skip after 3 failures — will retry if LedFx clears cache on stop
            return None

    def _ledfx_virtual_to_ip(self, vid, virtuals):
        """Legacy fallback — no longer used by main poll loop."""
        """Legacy fallback — no longer used by main poll loop."""
        return None

    async def _async_confirm_release(self, ip):
        """Called after WLED confirms live=False — unlock card. LedFx is stopped so hide badge."""
        name = self.cards.get(ip, {}).get("name_label")
        card_name = name.value if name else ip
        c = self.cards.get(ip)
        if c:
            c["live_badge"].visible = False
            try: c["live_badge"].update()
            except: pass
        self._set_card_unlive(ip, ping_delay=0)
        self.log(f"[Live] {card_name} — confirmed released by WLED", color="green400")

    async def _async_set_live(self, ip, live):
        """Run _set_card_live or _set_card_unlive on the Flet event loop."""
        name = self.cards.get(ip, {}).get("name_label")
        card_name = name.value if name else ip
        if live:
            self._set_card_live(ip)
            self.log(f"[LedFx] {card_name} — LedFx activated, controls locked", color="orange400")
        else:
            self._set_card_unlive(ip)
            self.log(f"[LedFx] {card_name} — LedFx released, controls restored", color="cyan")

    def toggle_ledfx(self, e):
        if self.is_ledfx_running():
            # Kill the running process
            for proc in psutil.process_iter(['name']):
                try:
                    if proc.info['name'] and proc.info['name'].lower() == "ledfx.exe":
                        proc.kill()
                        self.log("[LedFx] Process terminated.")
                except: pass
        else:
            if self.ledfx_path and os.path.exists(self.ledfx_path):
                self._launch_ledfx()
            else:
                # No path known — show install/browse dialog
                self._show_ledfx_setup_dialog()

    def _show_ledfx_setup_dialog(self):
        """Show dialog offering Fresh Install or Browse to existing exe."""
        def close(_):
            dlg.open = False
            self.page.update()
        def do_browse(_):
            dlg.open = False
            self.page.update()
            self.file_picker.pick_files(dialog_title="Select ledfx.exe", allowed_extensions=["exe"])
        def do_install(_):
            dlg.open = False
            self.page.update()
            threading.Thread(target=self._run_ledfx_install, daemon=True).start()

        dlg = ft.AlertDialog(
            title=ft.Text("LedFx Not Found"),
            content=ft.Column([
                ft.Text("LedFx path is unknown. What would you like to do?", size=13),
            ], tight=True, width=380),
            actions=[
                ft.ElevatedButton("INSTALL FRESH", icon=ft.Icons.DOWNLOAD_FOR_OFFLINE,
                    bgcolor="yellow700", color="black", on_click=do_install),
                ft.TextButton("Browse to exe", on_click=do_browse),
                ft.TextButton("Cancel", on_click=close),
            ]
        )
        self.page.overlay.append(dlg)
        dlg.open = True
        self.page.update()

    def _launch_ledfx(self):
        """Start ledfx.exe and open the web UI once it is ready."""
        for _b in self._ledfx_btns:
            _b.disabled = True; _b.text = "STARTING..."; _b.bgcolor = "orange800"
            try: _b.update()
            except: pass
        self.log("[LedFx] Launching background process...")

        def _start():
            self._ledfx_launching = True
            subprocess.Popen([self.ledfx_path])
            # Poll until process is running (max 30s)
            for i in range(30):
                time.sleep(1)
                remaining = 30 - i
                for _b in self._ledfx_btns:
                    _b.text = f"STARTING... ({remaining}s)"
                    try: _b.update()
                    except: pass
                try:
                    requests.get("http://localhost:8888", timeout=1)
                    self.log(f"[LedFx] Ready after {i+1}s. Use LEDFX UI button to open web interface.")
                    self._ledfx_launching = False
                    break
                except: pass
            else:
                self.log("[LedFx] Timed out waiting for web UI — try opening http://localhost:8888 manually.", color="red400")
            self._ledfx_launching = False
            self._ledfx_launching = False
            for _b in self._ledfx_btns:
                _b.text = "STOP LEDFX"; _b.bgcolor = "red800"; _b.disabled = False
                try: _b.update()
                except: pass

        threading.Thread(target=_start, daemon=True).start()

    def check_ledfx_updates(self):
        try:
            resp = requests.get(LEDFX_RELEASES_URL, timeout=10).json()
            self.ledfx_latest_ver = resp.get("tag_name", "").replace("v", "")
            path_missing = not self.ledfx_path or not os.path.exists(self.ledfx_path)
            needs_update = self.ledfx_latest_ver != self.ledfx_current_ver
            if needs_update and not path_missing:
                self.log(f"LedFx: installed v{self.ledfx_current_ver} → update available v{self.ledfx_latest_ver}", color="yellow700")
                for _u in self._ledfx_update_btns:
                    _u.text = "UPDATE LEDFX"; _u.visible = True
                self.page.update()
            else:
                if path_missing:
                    self.log(f"LedFx: not installed (latest: v{self.ledfx_latest_ver}) — use START LEDFX to install")
                else:
                    self.log(f"LedFx: v{self.ledfx_current_ver} (up to date)")
        except: pass

    def install_or_update_ledfx(self, e):
        """Button handler — routes to install engine on a background thread."""
        for _u in self._ledfx_update_btns:
            _u.disabled = True; _u.text = "WORKING..."; _u.bgcolor = "orange700"
            try: _u.update()
            except: pass
        self._open_log()
        threading.Thread(target=self._run_ledfx_install, daemon=True).start()

    def _run_ledfx_install(self):
        """Download the LedFx setup zip, extract and launch the installer, then prompt user to browse to exe."""
        import shutil
        zip_path = os.path.join(os.path.expanduser("~"), "ledfx_install.zip")
        extract_path = os.path.join(os.path.expanduser("~"), "ledfx_install_tmp")
        try:
            # 1. Fetch release info
            self.log("[LedFx] Fetching latest release info...")
            resp = requests.get(LEDFX_RELEASES_URL, timeout=10).json()
            assets = resp.get("assets", [])
            ver = resp.get("tag_name", "").replace("v", "")

            # 2. Find the setup zip — preferred over portable for proper system install
            download_url, target_name = None, ""
            portable_url, portable_name = None, ""
            for asset in assets:
                n = asset["name"].lower()
                if n.endswith(".zip") and "win" in n and ("x64" in n or "64" in n):
                    if "setup" in n:
                        download_url, target_name = asset["browser_download_url"], asset["name"]
                    else:
                        portable_url, portable_name = asset["browser_download_url"], asset["name"]
            # Fall back to portable only if no setup zip exists
            if not download_url and portable_url:
                download_url, target_name = portable_url, portable_name
            if not download_url:
                self.log("[LedFx] ERROR: No Windows zip asset found in release.", color="red400")
                return
            self.log(f"[LedFx] Downloading {target_name}...")

            # 3. Download with progress
            for _r, _pb, _pt in zip(self._progress_rows, self._progress_bars, self._percent_texts):
                _r.visible = True; _pb.value = 0; _pt.value = "0%"
                try: _r.update()
                except: pass

            with requests.get(download_url, stream=True, timeout=120) as r:
                r.raise_for_status()
                total = int(r.headers.get("content-length", 0))
                downloaded = 0
                with open(zip_path, "wb") as f:
                    for chunk in r.iter_content(chunk_size=512 * 1024):
                        f.write(chunk)
                        downloaded += len(chunk)
                        if total > 0:
                            pct = downloaded / total
                            for _r, _pb, _pt in zip(self._progress_rows, self._progress_bars, self._percent_texts):
                                _pb.value = pct; _pt.value = f"{int(pct*100)}%"
                                try: _r.update()
                                except: pass

            self.log("[LedFx] Download complete. Extracting...")

            # 4. Extract zip
            if os.path.exists(extract_path):
                shutil.rmtree(extract_path)
            with zipfile.ZipFile(zip_path, "r") as zf:
                zf.extractall(extract_path)

            # 5. Find all exes — log them so we can see what came out
            all_exes, found_setup, found_ledfx = [], None, None
            for root, dirs, files in os.walk(extract_path):
                for fname in files:
                    if fname.lower().endswith(".exe"):
                        full = os.path.join(root, fname)
                        all_exes.append(os.path.relpath(full, extract_path))
                        fl = fname.lower()
                        if "setup" in fl and "ledfx" in fl and not found_setup:
                            found_setup = full
                        elif fl == "ledfx.exe" and not found_ledfx:
                            found_ledfx = full

            self.log(f"[LedFx] Found in zip: {', '.join(all_exes) if all_exes else 'NO EXES FOUND'}")

            if found_setup:
                # Setup installer path — user picks install location
                self.log(f"[LedFx] Launching installer: {os.path.basename(found_setup)}")
                self.log("[LedFx] NOTE: User presets/config live in %APPDATA%/ledfx and are safe during reinstall.")
                self.log("[LedFx] After install completes, press START LEDFX and browse to ledfx.exe.")
                os.startfile(found_setup)
                # Update version and hide the update button — install is done
                self.ledfx_current_ver = ver
                self.save_cache()
                for _u in self._ledfx_update_btns:
                    _u.visible = False
                    try: _u.update()
                    except: pass

            elif found_ledfx:
                # Portable fallback — shouldn't normally happen if setup zip is available
                self.log("[LedFx] No setup exe found — using portable build.")
                self.log(f"[LedFx] ledfx.exe is at: {found_ledfx}")
                self.log("[LedFx] Press START LEDFX and browse to that path to use it.")
                self.ledfx_current_ver = ver
                self.save_cache()
                for _u in self._ledfx_update_btns:
                    _u.visible = False
                    try: _u.update()
                    except: pass
            else:
                self.log("[LedFx] ERROR: No usable exe found inside zip.", color="red400")

        except Exception as ex:
            self.log(f"[LedFx] UPDATE FAILED: {ex}", color="red400")
            # Only restore the button if there was a known path (i.e. this was an update, not install)
            if self.ledfx_path and os.path.exists(self.ledfx_path):
                for _u in self._ledfx_update_btns:
                    _u.disabled = False; _u.text = "UPDATE LEDFX"; _u.bgcolor = "yellow700"
                    try: _u.update()
                    except: pass
            else:
                for _u in self._ledfx_update_btns:
                    _u.visible = False
                    try: _u.update()
                    except: pass
        finally:
            for _r in self._progress_rows:
                _r.visible = False
                try: _r.update()
                except: pass
            # Cleanup in background — installer may still hold file locks
            def _deferred_cleanup(zp, ep):
                for attempt in range(24):  # retry for up to ~2 min
                    try:
                        if os.path.exists(zp): os.remove(zp)
                        if os.path.exists(ep): shutil.rmtree(ep)
                        self.log("[LedFx] Temp files cleaned up.")
                        return
                    except:
                        time.sleep(5)
                self.log("[LedFx] Could not clean temp files — you can delete them manually.")
                self.log(f"[LedFx]   {zp}")
                self.log(f"[LedFx]   {ep}")
            threading.Thread(target=_deferred_cleanup, args=(zip_path, extract_path), daemon=True).start()

    def on_file_result(self, e: ft.FilePickerResultEvent):
        """Called when user browses to an existing ledfx.exe."""
        if e.files:
            self.ledfx_path = e.files[0].path
            self.save_cache()
            self.log(f"[LedFx] Path set to: {self.ledfx_path}")
            for _u in self._ledfx_update_btns:
                _u.visible = False
                try: _u.update()
                except: pass
            self._launch_ledfx()

    def setup_ui(self):
        self.page.title = "WLED Command Center+"
        self.page.theme_mode = ft.ThemeMode.DARK
        self.page.bgcolor = "#0a0a0c"
        self.page.scroll = None  # page never scrolls — content column handles all scrolling
        # Restore saved window size, position and maximized state.
        # Strategy: start hidden, set all properties, then show.
        # This avoids the race condition that causes off-screen flashing.
        saved_w   = getattr(self, '_win_w', 1200)
        saved_h   = getattr(self, '_win_h', 800)
        saved_max = getattr(self, '_win_max', False)

        try:
            win = self.page.window
            win.min_width  = 700
            win.min_height = 500
            if not saved_max:
                win.width  = saved_w
                win.height = saved_h
            else:
                win.maximized = True
        except AttributeError:
            self.page.window_min_width  = 700
            self.page.window_min_height = 500
            if not saved_max:
                self.page.window_width  = saved_w
                self.page.window_height = saved_h
            else:
                self.page.window_maximized = True
        self.page.on_resized = self._on_window_resize
        
        def _section(title, color, *lines):
            return [
                ft.Container(height=6),
                ft.Text(title, weight="bold", color=color, size=13),
                *[ft.Text(l, size=12, color="grey300") for l in lines],
            ]

        manual_content = ft.Column(
            scroll=ft.ScrollMode.AUTO,
            width=520,
            height=520,
            spacing=2,
            controls=[
                ft.Text("WLED COMMAND CENTER+ — USER MANUAL", weight="bold", size=14, color="#00f2ff"),
                ft.TextButton(
                    content=ft.Text("by SullySSignS.ca", size=10, color="grey600"),
                    on_click=lambda _: self.page.launch_url("https://www.sullyssigns.ca"),
                    tooltip="Visit sullyssigns.ca",
                    style=ft.ButtonStyle(padding=ft.padding.only(top=0, bottom=0)),
                ),
                ft.Divider(),

                *_section("WHAT IS THIS PROGRAM?", "#00f2ff",
                    "WLED Command Center+ lets you control all your WLED, MagicHome, and",
                    "custom devices from one place. Devices are auto-discovered on startup",
                    "and kept in sync via background polling. All settings, names, scenes,",
                    "and card order are saved and restored between sessions.",
                ),

                *_section("TOP BAR — GLOBAL CONTROLS", "cyan",
                    "ALL OFF / ALL ON — Instantly powers every device off or on.",
                    "OPEN LOG — Shows the debug console. Drag the bottom edge to resize it.",
                    "  COPY LOG copies all text. CLEAR LOG wipes it. DEBUG toggles verbose",
                    "  logging. CLOSE LOG hides the panel.",
                    "  Session logs are also saved automatically to the app folder —",
                    "  up to 10 previous sessions are kept for review.",
                    "MANUAL — Opens this guide.",
                    "MERGE — Enables merge mode so you can drag one card onto another",
                    "  to combine them. Useful when a device reappeared with a new IP",
                    "  and created a duplicate card. Active when button turns orange.",
                    "  Click again to cancel. See DEVICE DISCOVERY for more details.",
                    "SCAN — Polls all devices for fresh status AND rescans the",
                    "  network for new devices. Use this after a router reboot or when",
                    "  a device changes IP.",
                    "MASTER BRIGHTNESS — Slides all device brightness together while",
                    "  preserving relative levels between devices.",
                    "SCENES — Row of scene buttons. See SCENES section below.",
                    "LEDFX UI — Appears beside STOP LEDFX while LedFx is running.",
                    "  Opens the LedFx web interface at localhost:8888 in your browser.",
                    "START/STOP LEDFX — See AUDIO SYNC section below.",
                ),

                *_section("DEVICE CARDS", "cyan",
                    "Each device gets its own card showing name, type badge, IP,",
                    "firmware version, chip type, WiFi signal, and current effect.",
                    "WLED cards show a cyan WLED badge. MagicHome cards show a green MH",
                    "badge. Custom/launcher cards show the site favicon.",
                    "Cards glow rainbow when on, dim when off, dark red when offline.",
                    "DRAG HANDLE (⠿) — Left edge of card. Drag to reorder.",
                    "  In MERGE mode, dropping onto another card offers Reorder or Merge.",
                    "✏ RENAME — Pencil icon. Give the device a friendly name.",
                    "✕ REMOVE — Red X removes a dead or unwanted card. If the device",
                    "  is still on the network it will reappear automatically on next scan.",
                    "POWER SWITCH — Toggles device on or off.",
                    "BRIGHTNESS SLIDER — Adjusts brightness in color mode, or controls",
                    "  effect speed in MagicHome effect mode. Label shows % or SPD.",
                    "🎨 COLOR — Rainbow button opens a color picker.",
                    "✨ PRESET / MODES — Opens saved presets (WLED) or built-in effects",
                    "  (MagicHome). For WLED, the app verifies the effect changed and",
                    "  retries automatically. For MagicHome, use the brightness slider",
                    "  to adjust speed after selecting an effect.",
                ),

                *_section("WLED-ONLY CONTROLS", "#00f2ff",
                    "OPEN WEB UI — Click the WLED badge to open the full WLED web UI.",
                    "SANITIZE — Strips brightness from saved presets so switching presets",
                    "  no longer changes your brightness unexpectedly. Device reboots",
                    "  automatically. Close the WLED web UI before running.",
                    "UPDATE — Appears when newer firmware is available. Downloads and",
                    "  flashes the correct build silently. Device reboots when done.",
                    "LIVE BADGE — Appears on all WLED cards whenever LedFx is running.",
                    "  ORANGE badge — LedFx currently has control of this device.",
                    "    Color and preset controls are locked. Power and brightness still work.",
                    "    Card border glows rainbow just like a powered-on device.",
                    "    Click to release this device back to WLED control — badge goes grey.",
                    "  GREY badge — LedFx is running but not controlling this device.",
                    "    All controls are fully available.",
                    "    Click to hand control of this device to LedFx — badge goes orange.",
                    "  Badges hide automatically when LedFx is stopped.",
                ),

                *_section("MAGICHOME NOTES", "#00ff88",
                    "MagicHome devices support color and built-in effects only.",
                    "No Sanitize or firmware update — those are WLED features.",
                    "Brightness works in static color mode. In effect mode, slider = speed.",
                    "Color changes switch back to static mode automatically.",
                    "Effects are selected from the MODES popup — 21 built-in patterns.",
                    "BRIGHTNESS SLIDER — Commands are only sent when you release the slider,",
                    "  not while dragging. This prevents flooding the device with rapid",
                    "  commands which can cause it to crash or reboot.",
                    "RATE LIMITING — A 1 second gap is enforced between all commands to",
                    "  the same MagicHome device. Rapid clicks are queued and spaced out",
                    "  automatically — the device will always receive the final state.",
                    "POWER ON VIA SLIDER — If the device is off and you move the brightness",
                    "  slider, the device powers on automatically then sets the brightness",
                    "  after a 1 second delay to ensure the device is ready.",
                ),

                *_section("SCENES", "#00f2ff",
                    "Scene buttons sit in the master bar. You always see your saved scenes",
                    "plus one ADD button. There is no limit — record as many as you need.",
                    "Each scene stores the full state of every device — on/off, brightness,",
                    "color, effect, and active WLED preset. Scenes use a stable internal ID",
                    "so they survive device IP changes and renames.",
                    "ADD SCENE (+) — Click empty slot to snapshot all devices now.",
                    "  Name the scene and press Enter or Save.",
                    "ACTIVATE — Click the scene name to restore all devices instantly.",
                    "  Offline devices are skipped with a note in the log.",
                    "✏ RENAME — Left pencil icon on scene button to change its name.",
                    "✕ CLEAR — X icon deletes the scene slot.",
                    "EDIT — Right icon opens the scene editor popup:",
                    "  • Checkbox per device — check to include, uncheck to exclude.",
                    "  • Refresh button per device — updates just that device's saved",
                    "    state to its current state without re-recording everything.",
                    "  • Newly checked devices are snapshotted at the moment you save.",
                    "Scenes are saved to disk and survive restarts.",
                ),

                *_section("AUDIO SYNC (LedFx)", "purple",
                    "START LEDFX — Launches LedFx and shows a countdown. Button stays",
                    "  on STARTING until LedFx web UI responds (up to 30s).",
                    "STOP LEDFX — Shuts down LedFx. Cards unlock after a short cooldown.",
                    "LEDFX UI — Opens the LedFx web interface in your browser. Only",
                    "  visible while LedFx is running, beside the STOP LEDFX button.",
                    "INSTALL / UPDATE LEDFX — Downloads and installs the latest version.",
                    "  After install, click START LEDFX and browse to ledfx.exe.",
                    "LIVE MODE — While LedFx runs, all WLED cards show a LIVE badge.",
                    "  The app polls LedFx every 3 seconds to track which devices are active.",
                    "  ORANGE badge — LedFx is actively controlling this device.",
                    "    Click to release it back to WLED. Badge turns grey.",
                    "  GREY badge — LedFx is running but not controlling this device.",
                    "    Click to hand it to LedFx. Badge turns orange.",
                    "  If you enable or disable a device inside the LedFx app directly,",
                    "  the badge updates automatically on the next poll (within 3 seconds).",
                    "  All badges hide when LedFx is stopped.",
                ),

                *_section("ADDING CUSTOM DEVICES", "grey400",
                    "The + ADD DEVICE card is always last in the grid.",
                    "Click it and enter an IP address, local hostname, or website URL.",
                    "  IP address — app probes for WLED, then TCP on port 80.",
                    "    If WLED found: adds a full WLED card automatically.",
                    "    If HTTP found: asks for a name and creates a launcher card.",
                    "  Hostname (e.g. house.local) — creates a launcher card.",
                    "  URL (e.g. sullyssigns.ca) — creates a launcher card with favicon.",
                    "Launcher cards show online/offline status (local devices),",
                    "  an OPEN button, editable name, and drag handle for reordering.",
                    "Custom cards are saved and restored between sessions.",
                ),

                *_section("DEVICE DISCOVERY & IP CHANGES", "grey400",
                    "WLED: discovered via mDNS. MagicHome: via broadcast on port 48899.",
                    "On startup, a 10-second scan runs automatically after 5 seconds.",
                    "If a device changes IP (e.g. after router reboot), click REFRESH.",
                    "  The app matches devices by MAC address — if a new IP is found for",
                    "  a known MAC, the cache is updated and a full restart applies it.",
                    "  MAC addresses are learned from WLED's /json API on first poll,",
                    "  so devices with friendly mDNS names (Ceiling.local etc) are",
                    "  matched correctly after the first session.",
                    "If a duplicate card appears, use MERGE mode: click MERGE in the",
                    "  top bar (turns orange), drag the new card onto the old card,",
                    "  and confirm. Old card keeps its name and scenes, new card removed.",
                ),



                ft.Container(height=10),
                ft.TextButton(
                    content=ft.Text("SullySSignS.ca", size=10, color="grey700"),
                    on_click=lambda _: self.page.launch_url("https://www.sullyssigns.ca"),
                    tooltip="Visit sullyssigns.ca",
                    style=ft.ButtonStyle(padding=ft.padding.only(top=0, bottom=0)),
                ),
            ]
        )

        self.help_dialog = ft.AlertDialog(
            title=ft.Text("WLED Command Center+ — Manual", color="#00f2ff"),
            content=manual_content,
            actions=[ft.ElevatedButton("Close", bgcolor="cyan", color="black",
                on_click=lambda _: (setattr(self.help_dialog, "open", False), self.page.update()))]
        )
        self.page.overlay.append(self.help_dialog)

        self.log_autoscroll = True
        self.log_lines = ft.ListView([], spacing=0, item_extent=16, auto_scroll=False)
        self._log_height = 180  # default height, adjustable by drag

        self.log_scroll_container = ft.Container(
            content=self.log_lines,
            height=self._log_height, bgcolor="#050507", border_radius=6,
            border=ft.border.all(1, "#2b2b3b"), padding=6,
        )
        self.autoscroll_btn = ft.TextButton(
            content=ft.Text("AUTO-SCROLL: ON", size=9, color="cyan", weight="bold"),
            on_click=self.toggle_autoscroll,
            style=ft.ButtonStyle(padding=ft.padding.symmetric(horizontal=6, vertical=2))
        )
        self.copy_log_btn = ft.TextButton(
            content=ft.Text("COPY LOG", size=9, color="grey400", weight="bold"),
            on_click=self.copy_log,
            style=ft.ButtonStyle(padding=ft.padding.symmetric(horizontal=6, vertical=2))
        )
        self.clear_log_btn = ft.TextButton(
            content=ft.Text("CLEAR LOG", size=9, color="grey400", weight="bold"),
            on_click=self.clear_log,
            style=ft.ButtonStyle(padding=ft.padding.symmetric(horizontal=6, vertical=2))
        )
        self.close_log_btn = ft.TextButton(
            content=ft.Text("CLOSE LOG", size=9, color="orange400", weight="bold"),
            on_click=self.toggle_logs,
            style=ft.ButtonStyle(padding=ft.padding.symmetric(horizontal=6, vertical=2))
        )
        self.open_folder_btn = ft.TextButton(
            content=ft.Text("OPEN FOLDER", size=9, color="grey400", weight="bold"),
            on_click=self.open_log_folder,
            tooltip=f"Open data folder in Explorer:\n{LOG_DIR}",
            style=ft.ButtonStyle(padding=ft.padding.symmetric(horizontal=6, vertical=2))
        )
        self._debug_btn_text = ft.Text("DEBUG: OFF", size=9, color="grey400", weight="bold")
        self.debug_btn = ft.TextButton(
            content=self._debug_btn_text,
            on_click=self.toggle_debug,
            style=ft.ButtonStyle(padding=ft.padding.symmetric(horizontal=6, vertical=2))
        )
        self.debug_on_open_cb = ft.Checkbox(
            label="DBG on open",
            value=self.debug_on_open,
            label_style=ft.TextStyle(size=9, color="grey500"),
            on_change=self._on_debug_on_open_change,
            scale=0.8,
            tooltip="When checked, debug mode turns ON automatically each time the log panel is opened",
        )
        self.log_auto_open_cb = ft.Checkbox(
            label="Auto-open",
            value=self.log_auto_open,
            label_style=ft.TextStyle(size=9, color="grey500"),
            on_change=self._on_log_auto_open_change,
            scale=0.8,
            tooltip="When checked, the log panel opens automatically at program start",
        )
        def _on_log_drag(e: ft.DragUpdateEvent):
            self._log_height = max(80, min(600, self._log_height + e.delta_y))
            self.log_scroll_container.height = self._log_height
            try: self.log_scroll_container.update()
            except: pass

        _drag_handle = ft.GestureDetector(
            on_vertical_drag_update=_on_log_drag,
            mouse_cursor=ft.MouseCursor.RESIZE_ROW,
            content=ft.Container(
                height=8,
                content=ft.Row([
                    ft.Container(width=40, height=3, bgcolor="grey700", border_radius=2),
                ], alignment="center"),
                bgcolor="#050507",
                border_radius=ft.border_radius.only(bottom_left=6, bottom_right=6),
            ),
        )

        self.log_container = ft.Container(
            content=ft.Column([
                ft.Row([
                    ft.Row([ft.Text("DEBUG CONSOLE", size=10, weight="bold", color="grey600"), self.autoscroll_btn, self.copy_log_btn, self.clear_log_btn, self.open_folder_btn, self.debug_btn, self.debug_on_open_cb, self.log_auto_open_cb, self.close_log_btn], spacing=6, vertical_alignment=ft.CrossAxisAlignment.CENTER),
                    ft.IconButton(ft.Icons.CLOSE, icon_size=14, on_click=self.toggle_logs)
                ], alignment="spaceBetween"),
                ft.Row([self.log_scroll_container], expand=True),
                _drag_handle,
            ], expand=True),
            visible=self.log_auto_open, expand=True, padding=10,
            border=ft.border.all(1, "#2b2b3b"), border_radius=8, margin=ft.margin.only(bottom=10)
        )
        self.log_scroll_container.expand = True

        self._refresh_icon = ft.Icon(ft.Icons.REFRESH, size=14, color="grey400")
        self._refresh_text = ft.Text("SCAN", size=11, color="grey400", weight="bold")
        self.refresh_btn = ft.ElevatedButton(
            content=ft.Row([self._refresh_icon, self._refresh_text], spacing=4, tight=True),
            on_click=self.on_refresh_click,
            bgcolor="#1e1e2a",
            style=ft.ButtonStyle(
                shape=ft.RoundedRectangleBorder(radius=6),
                side=ft.BorderSide(1, "#2b2b3b"),
            ),
        )
        # ledfx buttons — two instances each so both wide and narrow layouts stay in sync
        self.ledfx_btn_wide   = ft.ElevatedButton("START LEDFX", icon=ft.Icons.EQUALIZER, color="white", bgcolor="purple700", on_click=self.toggle_ledfx)
        self.ledfx_btn_narrow = ft.ElevatedButton("START LEDFX", icon=ft.Icons.EQUALIZER, color="white", bgcolor="purple700", on_click=self.toggle_ledfx)
        self.ledfx_ui_btn_wide   = ft.ElevatedButton("LEDFX UI", icon=ft.Icons.OPEN_IN_BROWSER, color="white", bgcolor="purple900", visible=False, on_click=lambda _: self.page.launch_url("http://localhost:8888"))
        self.ledfx_ui_btn_narrow = ft.ElevatedButton("LEDFX UI", icon=ft.Icons.OPEN_IN_BROWSER, color="white", bgcolor="purple900", visible=False, on_click=lambda _: self.page.launch_url("http://localhost:8888"))
        self.scene_toggle_btn_wide   = ft.ElevatedButton("LEDFX SCENES", icon=ft.Icons.SWAP_HORIZ, color="white", bgcolor="purple900", visible=False, on_click=self.toggle_scene_mode)
        self.scene_toggle_btn_narrow = ft.ElevatedButton("LEDFX SCENES", icon=ft.Icons.SWAP_HORIZ, color="white", bgcolor="purple900", visible=False, on_click=self.toggle_scene_mode)
        self.ledfx_update_btn_wide   = ft.ElevatedButton("UPDATE LEDFX", icon=ft.Icons.DOWNLOAD_FOR_OFFLINE, color="black", bgcolor="yellow700", visible=False, on_click=self.install_or_update_ledfx)
        self.ledfx_update_btn_narrow = ft.ElevatedButton("UPDATE LEDFX", icon=ft.Icons.DOWNLOAD_FOR_OFFLINE, color="black", bgcolor="yellow700", visible=False, on_click=self.install_or_update_ledfx)
        self.update_progress_bar_wide   = ft.ProgressBar(value=0, width=150, color="yellow700", bgcolor="#2b2b3b")
        self.update_progress_bar_narrow = ft.ProgressBar(value=0, width=150, color="yellow700", bgcolor="#2b2b3b")
        self.update_percent_text_wide   = ft.Text("0%", size=10, color="yellow700")
        self.update_percent_text_narrow = ft.Text("0%", size=10, color="yellow700")
        self.update_progress_row_wide   = ft.Row([self.update_progress_bar_wide,   self.update_percent_text_wide],   visible=False, spacing=10)
        self.update_progress_row_narrow = ft.Row([self.update_progress_bar_narrow, self.update_percent_text_narrow], visible=False, spacing=10)
        # Convenience lists for broadcasting state to both layouts at once
        self._ledfx_btns        = [self.ledfx_btn_wide,          self.ledfx_btn_narrow]
        self._ledfx_ui_btns     = [self.ledfx_ui_btn_wide,       self.ledfx_ui_btn_narrow]
        self._scene_toggle_btns = [self.scene_toggle_btn_wide,   self.scene_toggle_btn_narrow]
        self._ledfx_update_btns = [self.ledfx_update_btn_wide,   self.ledfx_update_btn_narrow]
        self._progress_bars     = [self.update_progress_bar_wide, self.update_progress_bar_narrow]
        self._percent_texts     = [self.update_percent_text_wide, self.update_percent_text_narrow]
        self._progress_rows     = [self.update_progress_row_wide, self.update_progress_row_narrow]
        

        # Build per-character title controls before the header Row so they
        # can be referenced inline without statements inside a list literal.
        self._title_chars = []
        for _ch in "WLED COMMAND CENTER+":
            self._title_chars.append(
                ft.Text(_ch, size=28, weight="bold", italic=True, color="#00f2ff")
            )

        # ── Title animation controls (near SullySigns) ───────────────────────
        self._title_speed_slider = ft.Slider(
            min=2, max=20, value=self.title_speed, width=80,
            active_color="cyan",
            on_change=lambda e: (setattr(self, "title_speed", float(e.control.value)), self.save_cache()),
        )
        _title_color_btn = ft.Container(
            width=28, height=28, border_radius=6,
            gradient=ft.LinearGradient(
                begin=ft.alignment.top_left, end=ft.alignment.bottom_right,
                colors=["#FF0000","#FF8800","#FFFF00","#00FF00","#00FFFF","#0000FF","#FF00FF","#FF0000"],
            ),
            border=ft.border.all(1, "#ffffff33"), tooltip="Title color",
            ink=True, on_click=lambda _: self.show_anim_color_picker("title"),
            content=ft.Icon(ft.Icons.COLORIZE, size=14, color="#ffffff88"),
        )
        _title_effect_btn = ft.Container(
            width=28, height=28, border_radius=6,
            bgcolor="#1a1a2e", border=ft.border.all(1, "#00f2ff44"),
            tooltip="Title effect", ink=True,
            on_click=lambda _: self.show_anim_effect_picker("title"),
            content=ft.Icon(ft.Icons.AUTO_AWESOME, size=14, color="#00f2ff"),
        )

        # ── Border animation controls (near SCAN) ─────────────────────────────
        self._border_speed_slider = ft.Slider(
            min=2, max=20, value=self.border_speed, width=80,
            active_color="cyan",
            on_change=lambda e: (setattr(self, "border_speed", float(e.control.value)), self.save_cache()),
        )
        _border_color_btn = ft.Container(
            width=28, height=28, border_radius=6,
            gradient=ft.LinearGradient(
                begin=ft.alignment.top_left, end=ft.alignment.bottom_right,
                colors=["#FF0000","#FF8800","#FFFF00","#00FF00","#00FFFF","#0000FF","#FF00FF","#FF0000"],
            ),
            border=ft.border.all(1, "#ffffff33"), tooltip="Border color",
            ink=True, on_click=lambda _: self.show_anim_color_picker("border"),
            content=ft.Icon(ft.Icons.COLORIZE, size=14, color="#ffffff88"),
        )
        _border_effect_btn = ft.Container(
            width=28, height=28, border_radius=6,
            bgcolor="#1a1a2e", border=ft.border.all(1, "#00f2ff44"),
            tooltip="Border effect", ink=True,
            on_click=lambda _: self.show_anim_effect_picker("border"),
            content=ft.Icon(ft.Icons.AUTO_AWESOME, size=14, color="#00f2ff"),
        )

        self.header = ft.Row([
            ft.Row([
                ft.Row(self._title_chars, spacing=0, tight=True),
                ft.Column([
                    ft.Text(f"v{APP_VERSION}", size=10, color="grey600"),
                    ft.TextButton(
                        content=ft.Text("by SullySSignS.ca", size=10, color="grey600"),
                        on_click=lambda _: self.page.launch_url("https://www.sullyssigns.ca"),
                        tooltip="Visit sullyssigns.ca",
                        style=ft.ButtonStyle(padding=ft.padding.all(0)),
                    ),
                ], spacing=0, tight=True),
                ft.Row([
                    self._title_speed_slider,
                    _title_color_btn,
                    _title_effect_btn,
                ], spacing=4, vertical_alignment=ft.CrossAxisAlignment.CENTER),
            ], vertical_alignment="end", spacing=6),
            ft.Row([
                ft.Row([
                    self._border_speed_slider,
                    _border_color_btn,
                    _border_effect_btn,
                ], spacing=4, vertical_alignment=ft.CrossAxisAlignment.CENTER),
                self.refresh_btn,
            ], spacing=10, vertical_alignment=ft.CrossAxisAlignment.CENTER),
        ], alignment="spaceBetween")
        
        self.scene_btns = []
        self._rebuild_scene_row_controls()

        # Two separate scene row instances — Flet cannot share one control across two parents.
        # Build independent button lists for each row from the start.
        self.scene_btn_refs.clear()
        _wide_init   = []
        _narrow_init = []
        for i in range(len(self.scenes)):
            if self.scenes[i] is not None:
                _wide_init.append(self._build_scene_btn(i))
                _narrow_init.append(self._build_scene_btn(i))
        for i in range(len(self.scenes)):
            if self.scenes[i] is None:
                _wide_init.append(self._build_scene_btn(i))
                _narrow_init.append(self._build_scene_btn(i))
                break

        self.scene_row_wide   = ft.Row(_wide_init,   spacing=6)
        self.scene_row_narrow = ft.Row(_narrow_init, spacing=6)

        # Each layout needs its own Slider instance for the same reason.
        _slider_wide   = ft.Slider(min=0, max=255, value=self.current_master_bri,
            active_color="cyan", expand=True, on_change=self.handle_master_brightness)
        _slider_narrow = ft.Slider(min=0, max=255, value=self.current_master_bri,
            active_color="cyan", expand=True, on_change=self.handle_master_brightness)
        self._master_sliders = [_slider_wide, _slider_narrow]
        self._slider_actual_width = 999  # estimated in _should_use_narrow from window width

        # Controls that are truly shared (buttons, not rendered in the tree twice simultaneously)
        _all_off  = ft.ElevatedButton("ALL OFF", on_click=lambda _: self.broadcast_power(False), bgcolor="red900", color="white")
        _all_on   = ft.ElevatedButton("ALL ON",  on_click=lambda _: self.broadcast_power(True),  bgcolor="green900", color="white")
        _log_btn  = ft.TextButton(
            content=ft.Row([ft.Icon(ft.Icons.TERMINAL, size=16, color="grey400"), ft.Text("OPEN LOG", size=10, color="grey400")], spacing=4, tight=True),
            on_click=self.toggle_logs, style=ft.ButtonStyle(padding=ft.padding.symmetric(horizontal=8, vertical=6)))
        _man_btn  = ft.TextButton(
            content=ft.Row([ft.Icon(ft.Icons.HELP_OUTLINE, size=16, color="grey400"), ft.Text("MANUAL", size=10, color="grey400")], spacing=4, tight=True),
            on_click=self.show_help, style=ft.ButtonStyle(padding=ft.padding.symmetric(horizontal=8, vertical=6)))
        self._merge_btn_icon = ft.Icon(ft.Icons.MERGE, size=16, color="grey400")
        self._merge_btn_text = ft.Text("MERGE", size=10, color="grey400")
        _merge_btn = ft.TextButton(
            content=ft.Row([self._merge_btn_icon, self._merge_btn_text], spacing=4, tight=True),
            on_click=self.start_merge_mode, style=ft.ButtonStyle(padding=ft.padding.symmetric(horizontal=8, vertical=6)),
            tooltip="Drag a new card onto an old card to replace its IP")

        # ledfx rows — the same button instances are referenced in both layouts.
        # Since only one layout is visible at a time and these controls are never
        # dynamically reparented, Flet handles this correctly.
        _ledfx_row_wide   = ft.Row([self.update_progress_row_wide,   self.ledfx_update_btn_wide,   self.ledfx_ui_btn_wide,   self.ledfx_btn_wide])
        _ledfx_row_narrow = ft.Row([self.update_progress_row_narrow, self.ledfx_update_btn_narrow, self.ledfx_ui_btn_narrow, self.ledfx_btn_narrow])

        _bri_row_wide   = ft.Row([
            _slider_wide,
            self.scene_toggle_btn_wide,
            self.scene_row_wide,
        ], spacing=8, vertical_alignment=ft.CrossAxisAlignment.CENTER)

        _bri_row_narrow = ft.Row([
            self.scene_toggle_btn_narrow,
            self.scene_row_narrow,
        ], spacing=8, vertical_alignment=ft.CrossAxisAlignment.CENTER)

        # WIDE layout — single row, all controls side by side
        self._master_wide = ft.Row([
            ft.Column([ft.Text("GLOBAL POWER", size=10, color="grey500"),
                ft.Row([_all_off, _all_on, _log_btn, _man_btn, _merge_btn], spacing=4)], tight=True),
            ft.Column([
                _bri_row_wide,
            ], expand=True, horizontal_alignment="center"),
            ft.Column([ft.Text("AUDIO SYNC", size=10, color="grey500"), _ledfx_row_wide],
                horizontal_alignment="end"),
        ], alignment="spaceBetween", visible=True)

        # NARROW layout — row 1: power+slider+ledfx, row 2: scenes only
        self._master_narrow = ft.Column([
            ft.Row([
                ft.Column([ft.Text("GLOBAL POWER", size=10, color="grey500"),
                    ft.Row([_all_off, _all_on, _log_btn, _man_btn], spacing=4)], tight=True),
                ft.Container(content=_slider_narrow, expand=True),
                ft.Column([ft.Text("AUDIO SYNC", size=10, color="grey500"), _ledfx_row_narrow],
                    horizontal_alignment="end"),
            ], alignment="spaceBetween", vertical_alignment=ft.CrossAxisAlignment.END),
            ft.Row([
                self.scene_toggle_btn_narrow,
                self.scene_row_narrow,
            ], spacing=8, vertical_alignment=ft.CrossAxisAlignment.CENTER),
        ], spacing=8, visible=False)

        self.master_bar = ft.Container(
            content=ft.Column([self._master_wide, self._master_narrow], spacing=0),
            padding=15, bgcolor="#121218", border_radius=10, border=ft.border.all(1, "#2b2b3b")
        )
        
        self.device_list = ft.ResponsiveRow(spacing=15, run_spacing=15, columns=60)
        self.log_row = ft.Row([self.log_container], expand=False)
        self.log_container.expand = True
        # Wrap device list in its own scrollable container that fills remaining space.
        # This means page never scrolls — log and device list each scroll independently.
        self._device_scroll = ft.Column(
            [self.device_list],
            scroll=ft.ScrollMode.ADAPTIVE,
            expand=True,
        )
        self._main_col = ft.Column(
            [self.log_row, self.header, self.master_bar,
             ft.Divider(height=10, color="transparent"), self._device_scroll],
            scroll=None,
            expand=True,
        )
        self.page.add(self._main_col)
        # Apply correct col width immediately based on starting window size
        try:
            w = self.page.window.width or 1200
        except:
            w = getattr(self.page, 'window_width', 1200) or 1200
        self._apply_col_width(w)
        self._apply_master_layout(w)
        
        # Add cards in saved visual order, then any new devices not yet in the order list
        ordered_ips = [ip for ip in self.card_order if ip in self.cached_data]
        remaining_ips = [ip for ip in self.cached_data if ip not in self.card_order]
        for ip in ordered_ips + remaining_ips:
            name = self.cached_data[ip]
            self.add_device_card(name, ip, initial_online=False, dev_type=self.device_types.get(ip, "wled"))
        # Restore custom devices
        for key, info in self.custom_devices.items():
            self._add_custom_card(key, info["name"], info["url"], info.get("is_local", False), is_exe=info.get("is_exe", False))
        # Always show the + add device card last
        self._add_card_placeholder()

    # ── Scene management ─────────────────────────────────────────────────────

    def _rebuild_scene_row_controls(self):
        """Rebuild scene_btns list: all filled slots + exactly one empty slot."""
        self.scene_btns.clear()
        for i in range(len(self.scenes)):
            if self.scenes[i] is not None:
                self.scene_btns.append(self._build_scene_btn(i))
        # Find first empty slot index and add one ADD button
        for i in range(len(self.scenes)):
            if self.scenes[i] is None:
                self.scene_btns.append(self._build_scene_btn(i))
                break
        # If all 4 are full, append a 5th slot dynamically
        if all(s is not None for s in self.scenes):
            self.scenes.append(None)
            self.scene_btns.append(self._build_scene_btn(len(self.scenes)-1))

    def _build_scene_btn(self, idx):
        """Build a compact scene slot button to sit beside the brightness slider."""
        scene = self.scenes[idx] if idx < len(self.scenes) else None
        if scene is None:
            btn = ft.Container(
                width=110, height=44,
                border_radius=6,
                border=ft.border.all(1, "#2b2b3b"),
                bgcolor="#1e1e2a",
                ink=True,
                tooltip="Record current state as a scene",
                on_click=lambda _, i=idx: self.record_scene(i),
                content=ft.Row([
                    ft.Icon(ft.Icons.ADD, size=12, color="grey500"),
                    ft.Text("ADD SCENE", size=9, color="grey500", weight="bold"),
                ], alignment="center", spacing=4),
            )
        else:
            btn = ft.Container(
                width=110, height=44,
                border_radius=6,
                border=ft.border.all(1, "#2b2b3b"),
                bgcolor="#1e1e2a",
                padding=ft.padding.symmetric(horizontal=4, vertical=4),
                content=ft.Column([
                    ft.Container(
                        content=ft.Text(scene["name"], size=10, weight="bold",
                            color="#00f2ff", max_lines=1, overflow="ellipsis",
                            text_align="center"),
                        ink=True, border_radius=3,
                        tooltip="Activate scene",
                        on_click=lambda _, i=idx: self.activate_scene(i),
                    ),
                    ft.Row([
                        ft.IconButton(ft.Icons.EDIT, icon_size=10, icon_color="grey600",
                            tooltip="Rename", padding=ft.padding.all(2),
                            on_click=lambda _, i=idx: self.rename_scene(i)),
                        ft.IconButton(ft.Icons.CLOSE, icon_size=10, icon_color="red400",
                            tooltip="Clear", padding=ft.padding.all(2),
                            on_click=lambda _, i=idx: self.clear_scene(i)),
                        ft.IconButton(ft.Icons.TUNE, icon_size=10, icon_color="cyan",
                            tooltip="Edit scene devices", padding=ft.padding.all(2),
                            on_click=lambda _, i=idx: self.edit_scene(i)),
                    ], spacing=0, alignment="center"),
                ], spacing=0, tight=True, horizontal_alignment="center"),
            )
        if scene is not None:
            if idx not in self.scene_btn_refs:
                self.scene_btn_refs[idx] = []
            # Store (container, name_text) so activate_scene can update label
            _name_text = btn.content.controls[0].content
            self.scene_btn_refs[idx].append((btn, _name_text))
        elif idx in self.scene_btn_refs:
            del self.scene_btn_refs[idx]
        return btn

    def _refresh_scene_btn(self, idx):
        """Rebuild all scene buttons and sync both wide and narrow scene rows.
        If in LedFx scene mode, delegates to _rebuild_scene_rows_for_mode instead.
        """
        if self._scene_mode == "ledfx":
            self._rebuild_scene_rows_for_mode()
            return
        # Clear refs so _build_scene_btn can repopulate them fresh (list per slot)
        self.scene_btn_refs.clear()
        wide_btns   = []
        narrow_btns = []
        for i in range(len(self.scenes)):
            if self.scenes[i] is not None:
                wide_btns.append(self._build_scene_btn(i))
                narrow_btns.append(self._build_scene_btn(i))
        # Add exactly one ADD button for the first empty slot
        for i in range(len(self.scenes)):
            if self.scenes[i] is None:
                wide_btns.append(self._build_scene_btn(i))
                narrow_btns.append(self._build_scene_btn(i))
                break
        # If all slots are full, _build_scene_btn already expanded self.scenes; add the new slot
        if all(s is not None for s in self.scenes):
            self.scenes.append(None)
            wide_btns.append(self._build_scene_btn(len(self.scenes) - 1))
            narrow_btns.append(self._build_scene_btn(len(self.scenes) - 1))
        self.scene_row_wide.controls.clear()
        self.scene_row_wide.controls.extend(wide_btns)
        self.scene_row_narrow.controls.clear()
        self.scene_row_narrow.controls.extend(narrow_btns)
        # Recalculate layout — adding scenes may force switch to narrow
        try:
            w = self.page.window.width or 1200
        except AttributeError:
            w = getattr(self.page, "window_width", 1200) or 1200
        self._apply_master_layout(w)
        try:
            self.master_bar.update()
        except:
            try: self.page.update()
            except: pass

    def _fetch_ledfx_scenes(self):
        """Fetch scenes from LedFx API and store in ledfx_scenes."""
        try:
            r = requests.get("http://localhost:8888/api/scenes", timeout=3).json()
            scenes = r.get("scenes", {})
            if isinstance(scenes, list):
                scenes = {s["id"]: s.get("name", s["id"]) for s in scenes}
            else:
                scenes = {sid: s.get("name", sid) for sid, s in scenes.items()}
            self.ledfx_scenes = scenes
            self.log(f"[LedFx] Fetched {len(scenes)} scene(s) from LedFx", color="grey500")
        except Exception as e:
            self.log(f"[LedFx] Could not fetch scenes: {e}", color="orange400")
        # Restore toggle button text and rebuild row regardless of success/failure
        if self._scene_mode == "ledfx":
            for _t in self._scene_toggle_btns:
                _t.text = "WLED SCENES"
                _t.bgcolor = "cyan"
                _t.color = "black"
                try: _t.update()
                except: pass
            self._rebuild_scene_rows_for_mode()

    def toggle_scene_mode(self, e=None):
        """Toggle between WLED and LedFx scene sets."""
        if self._scene_mode == "wled":
            self._scene_mode = "ledfx"
            for _t in self._scene_toggle_btns:
                _t.text = "LOADING..."
                _t.bgcolor = "grey700"
                _t.color = "white"
                try: _t.update()
                except: pass
            self.log("[Scene] Switched to LedFx scenes", color="purple")
            # Always fetch fresh scene list from LedFx when switching to LedFx mode
            threading.Thread(target=self._fetch_ledfx_scenes, daemon=True).start()
            return  # _fetch_ledfx_scenes rebuilds the row when done
        else:
            self._scene_mode = "wled"
            for _t in self._scene_toggle_btns:
                _t.text = "LEDFX SCENES"
                _t.bgcolor = "purple900"
                _t.color = "white"
                try: _t.update()
                except: pass
            self.log("[Scene] Switched to WLED scenes", color="cyan")
        self._rebuild_scene_rows_for_mode()

    def _rebuild_scene_rows_for_mode(self):
        """Rebuild scene rows based on current _scene_mode."""
        if self._scene_mode == "ledfx":
            wide_btns   = [self._build_ledfx_scene_btn(sid, name)
                           for sid, name in self.ledfx_scenes.items()]
            narrow_btns = [self._build_ledfx_scene_btn(sid, name)
                           for sid, name in self.ledfx_scenes.items()]
            if not wide_btns:
                _empty = ft.Text("No LedFx scenes", size=10, color="grey600", italic=True)
                wide_btns   = [_empty]
                narrow_btns = [ft.Text("No LedFx scenes", size=10, color="grey600", italic=True)]
        else:
            # Rebuild WLED scene buttons fresh
            self.scene_btn_refs.clear()
            wide_btns, narrow_btns = [], []
            for i in range(len(self.scenes)):
                if self.scenes[i] is not None:
                    wide_btns.append(self._build_scene_btn(i))
                    narrow_btns.append(self._build_scene_btn(i))
            for i in range(len(self.scenes)):
                if self.scenes[i] is None:
                    wide_btns.append(self._build_scene_btn(i))
                    narrow_btns.append(self._build_scene_btn(i))
                    break
        self.scene_row_wide.controls.clear()
        self.scene_row_wide.controls.extend(wide_btns)
        self.scene_row_narrow.controls.clear()
        self.scene_row_narrow.controls.extend(narrow_btns)
        try:
            w = self.page.window.width or 1200
        except AttributeError:
            w = getattr(self.page, "window_width", 1200) or 1200
        self._apply_master_layout(w)
        try:
            self.master_bar.update()
        except:
            try: self.page.update()
            except: pass

    def _build_ledfx_scene_btn(self, scene_id, scene_name):
        """Build a LedFx scene activation button matching WLED scene button style."""
        def _activate(_):
            def _send():
                try:
                    r = requests.put("http://localhost:8888/api/scenes",
                                     json={"action": "activate", "id": scene_id}, timeout=3)
                    if r.status_code in (200, 204):
                        self.log(f"[LedFx Scene] '{scene_name}' activated", color="purple")
                    else:
                        self.log(f"[LedFx Scene] '{scene_name}' failed: HTTP {r.status_code}", color="red400")
                except Exception as ex:
                    self.log(f"[LedFx Scene] '{scene_name}' error: {ex}", color="red400")
            threading.Thread(target=_send, daemon=True).start()

        return ft.Container(
            width=110, height=44,
            border_radius=6,
            border=ft.border.all(1, "purple700"),
            bgcolor="#1a1a2e",
            padding=ft.padding.symmetric(horizontal=4, vertical=4),
            ink=True,
            tooltip=f"Activate LedFx scene: {scene_name}",
            on_click=_activate,
            content=ft.Column([
                ft.Container(
                    content=ft.Text(scene_name, size=10, weight="bold",
                        color="purple200", max_lines=1, overflow="ellipsis",
                        text_align="center"),
                    border_radius=3,
                ),
                ft.Row([
                    ft.Icon(ft.Icons.EQUALIZER, size=12, color="purple400"),
                ], spacing=0, alignment="center"),
            ], spacing=0, tight=True, horizontal_alignment="center"),
        )

    def _migrate_scenes(self, raw_scenes):
        """Convert old IP-keyed scene data to card-ID-keyed. Safe to call on already-migrated data."""
        migrated = []
        for slot in raw_scenes:
            if slot is None:
                migrated.append(None)
                continue
            old_data = slot.get("data", {})
            new_data = {}
            for key, state in old_data.items():
                # If key is already a UUID (36 chars with dashes), keep as-is
                if len(key) == 36 and key.count('-') == 4:
                    new_data[key] = state
                else:
                    # key is an IP — look up its card ID
                    cid = self.card_ids.get(key)
                    if cid:
                        new_data[cid] = state
                    else:
                        # No card ID yet — keep IP temporarily, will be fixed on next save
                        new_data[key] = state
            migrated.append({"name": slot["name"], "data": new_data})
        return migrated

    def _hex_to_name(self, hex_color):
        """Convert common hex color to a friendly name, fallback to hex."""
        names = {
            "#ff0000": "red",       "#ff1100": "red",
            "#00ff00": "green",     "#008000": "dark green",
            "#0000ff": "blue",      "#000080": "navy",
            "#ffff00": "yellow",    "#ffa500": "orange",
            "#ff8800": "orange",
            "#ff00ff": "magenta",   "#800080": "purple",
            "#00ffff": "cyan",      "#008080": "teal",
            "#ffffff": "white",     "#000000": "black",
            "#ff69b4": "pink",      "#ffc0cb": "pink",
            "#a52a2a": "#a52a2a",
            "#ff4500": "red-orange",
            "#7fff00": "chartreuse",
            "#4b0082": "indigo",    "#ee82ee": "violet",
            "#f5deb3": "wheat",     "#d2691e": "chocolate",
            "#40e0d0": "turquoise", "#e0ffff": "light cyan",
            "#ffe4b5": "moccasin",  "#ffdead": "navajo white",
        }
        h = hex_color.lower().strip()
        return names.get(h, hex_color)

    # ── Add-device card ──────────────────────────────────────────────────────

    def _add_card_placeholder(self):
        """Add/refresh the + Add Device card at the end of the device list."""
        # Remove existing placeholder if present
        for ctrl in list(self.device_list.controls):
            if getattr(ctrl, "data", None) == "__add_device__":
                self.device_list.controls.remove(ctrl)
        try:
            _cur_w = self.page.window.width or 1200
        except AttributeError:
            _cur_w = getattr(self.page, 'window_width', 1200) or 1200
        _col_map = {1: 60, 2: 30, 3: 20, 4: 15, 5: 12}
        _cur_col = _col_map[self._cols_for_width(_cur_w)]
        placeholder = ft.Container(
            data="__add_device__",
            col=_cur_col,
            content=ft.Container(
                border=ft.border.all(2, "#2b2b3b"),
                border_radius=12,
                bgcolor="#0e0e14",
                ink=True,
                on_click=self._show_add_device_dialog,
                tooltip="Add a new device",
                content=ft.Column([
                    ft.Icon(ft.Icons.ADD_CIRCLE_OUTLINE, size=32, color="#2b2b3b"),
                    ft.Text("ADD DEVICE", size=10, color="#2b2b3b", weight="bold"),
                ], alignment="center", horizontal_alignment="center", spacing=6),
                padding=ft.padding.symmetric(vertical=24),
            ),
        )
        self.device_list.controls.append(placeholder)
        try: self.device_list.update()
        except: pass

    def _show_add_device_dialog(self, e=None):
        """Show dialog for user to enter IP or URL to add a device."""
        field = ft.TextField(
            hint_text="192.168.0.x  or  house.local  or  sullyssigns.ca  or  C:\\path\\to\\app.exe",
            autofocus=True, border_color="cyan", width=400,
            on_submit=lambda e: _probe(e),
        )
        status_text = ft.Text("", size=11, color="grey400")

        def _probe(_):
            val = field.value.strip()
            # Don't lowercase exe paths — Windows paths are case-sensitive for display
            if not val.lower().endswith(".exe"):
                val = val.lower()
            if not val:
                return
            status_text.value = f"Probing {val}..."
            status_text.color = "grey400"
            try: status_text.update()
            except: pass
            threading.Thread(target=_do_probe, args=(val,), daemon=True).start()

        def _do_probe(val):
            # Check if already have a card for this IP/URL
            if val in self.cards or val in self.custom_devices:
                existing_name = (self.cards[val]["name_label"].value
                                 if val in self.cards else self.custom_devices[val]["name"])
                status_text.value = f"Already have a card for this: '{existing_name}'"
                status_text.color = "orange400"
                try: status_text.update()
                except: pass
                return
            # Also check by IP if a card exists with same IP
            if val in self.devices:
                existing_name = self.cards.get(val, {}).get("name_label")
                name = existing_name.value if existing_name else val
                status_text.value = f"Already have a card for this: '{name}'"
                status_text.color = "orange400"
                try: status_text.update()
                except: pass
                return

            # Exe path — skip network probing, go straight to name prompt
            if val.lower().endswith(".exe"):
                if not os.path.exists(val):
                    status_text.value = f"File not found: {val}"
                    status_text.color = "red400"
                    try: status_text.update()
                    except: pass
                    return
                _prompt_custom_name(val, val, False, is_exe=True)
                return

            # Determine if this looks like a local IP or hostname vs external URL
            import re
            is_ip = bool(re.match(r'^\d+\.\d+\.\d+\.\d+$', val))
            is_local = is_ip or val.endswith('.local') or not '.' in val.split('.')[-1].rstrip('/')

            if is_ip:
                # Step 1 — Try WLED (safe read-only GET)
                try:
                    r = requests.get(f"http://{val}/json", timeout=2.0).json()
                    if "state" in r and "info" in r:
                        dlg.open = False
                        self.page.update()
                        self.page.run_task(self.async_add, r["info"].get("name", val), val, "wled")
                        self.log(f"[Add] Found WLED device at {val}", color="green400")
                        return
                except: pass
                # Step 2 — Safe TCP connect on port 80 only — no data sent
                # MagicHome probe deliberately skipped to avoid sending commands to unknown devices
                alive = False
                try:
                    s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
                    s.settimeout(1.5)
                    s.connect((val, 80))
                    s.close()
                    alive = True
                except: pass
                if alive:
                    _prompt_custom_name(val, f"http://{val}", True)
                    return
                status_text.value = f"Nothing responded at {val} — check IP and try again"
                status_text.color = "red400"
                try: status_text.update()
                except: pass
            else:
                # URL or hostname — just create a launcher card, no probing
                url = val if val.startswith("http") else f"https://{val}"
                _prompt_custom_name(val, url, False)

        def _prompt_custom_name(key, url, is_local, is_exe=False):
            default_name = os.path.splitext(os.path.basename(key))[0].upper() if is_exe else key.split('/')[0].upper()
            name_field = ft.TextField(
                value=default_name,
                autofocus=True, border_color="cyan", width=320,
                label="Device name",
                on_submit=lambda e: _add(e),
            )
            def _add(_):
                name = name_field.value.strip() or key
                dlg.open = False
                self.page.update()
                self.custom_devices[key] = {"name": name, "url": url, "is_local": is_local, "is_exe": is_exe}
                self.save_cache()
                self._add_custom_card(key, name, url, is_local, is_exe=is_exe)
                self._add_card_placeholder()
                self.log(f"[Add] Added '{name}' → {url}", color="green400")
            # Update dialog content to name prompt
            dlg.title = ft.Text("Name this program" if is_exe else "Name this device", color="cyan")
            dlg.content = ft.Column([
                ft.Text(f"{'Program' if is_exe else 'Found'}: {url}", size=11, color="grey400"),
                name_field,
            ], tight=True, spacing=10, width=360)
            dlg.actions = [
                ft.ElevatedButton("Add", bgcolor="cyan", color="black", on_click=_add),
                ft.TextButton("Cancel", on_click=lambda _: (setattr(dlg, "open", False), self.page.update())),
            ]
            try: dlg.update()
            except: self.page.update()

        def _cancel(_):
            dlg.open = False
            self.page.update()

        dlg = ft.AlertDialog(
            title=ft.Text("Add Device", color="cyan"),
            content=ft.Column([
                ft.Text("Enter an IP address, local hostname, or web URL:", size=12, color="grey400"),
                field,
                status_text,
            ], tight=True, spacing=10, width=380),
            actions=[
                ft.ElevatedButton("Probe", bgcolor="cyan", color="black", on_click=_probe),
                ft.TextButton("Cancel", on_click=_cancel),
            ]
        )
        self.page.overlay.append(dlg)
        dlg.open = True
        self.page.update()

    def _add_custom_card(self, key, name, url, is_local, is_exe=False):
        """Build and add a custom launcher card matching standard card layout with drag support."""
        if key in self.cards: return

        # Restore is_exe from cache if not passed directly (e.g. on app restart)
        if not is_exe:
            is_exe = self.custom_devices.get(key, {}).get("is_exe", False)

        display_name = self.custom_names.get(key, name)
        name_label = ft.Text(display_name, weight="bold", size=16)
        status = ft.Text("CHECKING..." if is_local else "", size=12, color="grey500", weight="bold")
        status.visible = True
        info_text = ft.Text(url, size=10, color="grey500")

        edit_btn = ft.IconButton(ft.Icons.EDIT, icon_size=13, icon_color="grey500",
            tooltip="Rename", on_click=lambda _, k=key: self.show_rename_dialog(k))

        if is_exe:
            # Exe card — show program icon and LAUNCH button
            type_tag = ft.Container(
                content=ft.Icon(ft.Icons.TERMINAL, size=14, color="green400"),
                padding=ft.padding.symmetric(3, 5), border_radius=4,
                bgcolor="#1e1e2a", border=ft.border.all(1, "#2b2b3b"),
                tooltip=url,
            )
            def _launch_exe(_, path=url):
                try:
                    subprocess.Popen([path])
                    self.log(f"[App] Launched '{name}' ({path})", color="green400")
                except Exception as ex:
                    self.log(f"[App] Failed to launch '{name}': {ex}", color="red400")
            open_btn = ft.ElevatedButton(
                content=ft.Row([ft.Icon(ft.Icons.PLAY_ARROW, size=14), ft.Text("LAUNCH", size=11, weight="bold")], spacing=4, tight=True),
                bgcolor="#1a1a2e", color="white",
                on_click=_launch_exe,
                style=ft.ButtonStyle(shape=ft.RoundedRectangleBorder(radius=6)),
            )
        else:
            # URL/web card — favicon and OPEN button
            _domain = url.replace("https://","").replace("http://","").split("/")[0]
            favicon_url = f"https://t2.gstatic.com/faviconV2?client=SOCIAL&type=FAVICON&fallback_opts=TYPE,SIZE,URL&url=https://{_domain}&size=64"
            type_tag = ft.Container(
                content=ft.Image(src=favicon_url, width=16, height=16, fit=ft.ImageFit.CONTAIN,
                    error_content=ft.Icon(ft.Icons.LANGUAGE, size=14, color="grey500")),
                padding=ft.padding.symmetric(3, 5), border_radius=4,
                bgcolor="#1e1e2a", border=ft.border.all(1, "#2b2b3b"),
                tooltip=url,
            )
            open_btn = ft.ElevatedButton(
                content=ft.Row([ft.Icon(ft.Icons.OPEN_IN_BROWSER, size=14), ft.Text("OPEN", size=11, weight="bold")], spacing=4, tight=True),
                bgcolor="#1a1a2e", color="white",
                on_click=lambda _, u=url: self.page.launch_url(u),
                style=ft.ButtonStyle(shape=ft.RoundedRectangleBorder(radius=6)),
            )

        # Match standard card layout exactly — 3 rows + drag handle
        card = ft.Container(
            data=key, bgcolor="#16161e", border_radius=12,
            padding=ft.padding.only(left=12, right=12, top=10, bottom=10),
            content=ft.Column([
                # ROW 1: favicon tag | name | ✏ | ✕ | spacer
                ft.Row([
                    type_tag, name_label, edit_btn,
                    ft.IconButton(ft.Icons.CLOSE, icon_size=13, icon_color="red400",
                        tooltip="Remove", on_click=lambda _, k=key: self._remove_custom_card(k)),
                    ft.Container(expand=True),
                ], vertical_alignment="center", spacing=4),
                # ROW 2: info + status on left, OPEN button on right
                ft.Row([
                    ft.Column([info_text, status], spacing=2, expand=True),
                    open_btn,
                ], vertical_alignment="center", spacing=6),
                # ROW 3: spacer to match card height of standard cards
                ft.Container(height=28),
            ], spacing=6),
        )

        glow = ft.Container(content=card, border_radius=13,
            border=ft.border.all(2, "#2b2b3b"), bgcolor="#16161e", padding=2)

        # Drag handle — same as standard cards
        feedback = ft.Container(
            content=ft.Text(display_name, color="white", size=13, weight="bold"),
            bgcolor="#00f2ff22", border_radius=8, padding=10,
            border=ft.border.all(1, "#00f2ff"))
        handle_draggable = ft.Draggable(
            group="cards", data=key,
            content=ft.Container(
                content=ft.Icon(ft.Icons.DRAG_INDICATOR, size=20, color="grey500"),
                tooltip="Drag to reorder",
                padding=ft.padding.only(right=6, top=4, bottom=4),
                border_radius=6, ink=True,
            ),
            content_feedback=feedback,
        )
        self.draggable_map[str(id(handle_draggable))] = key

        card_with_handle = ft.Row([
            handle_draggable,
            ft.Container(content=glow, expand=True),
        ], spacing=0)

        drag_target = ft.DragTarget(
            group="cards", content=card_with_handle,
            on_accept=lambda e, tgt=key: self.drag_card(self._parse_drag_src(e.data), tgt),
            on_will_accept=lambda e, src=key: self._parse_drag_src(e.data) != src,
        )

        try:
            _cur_w = self.page.window.width or 1200
        except AttributeError:
            _cur_w = getattr(self.page, 'window_width', 1200) or 1200
        _col_map = {1: 60, 2: 30, 3: 20, 4: 15, 5: 12}
        cell = ft.Container(content=drag_target, col=_col_map[self._cols_for_width(_cur_w)], data=key)

        self.cards[key] = {
            "card": card, "glow": glow, "cell": cell,
            "handle": handle_draggable,
            "name_label": name_label, "status": status,
            "info_text": info_text, "_glow_state": "offline",
            "_is_custom": True, "_url": url, "_is_local": is_local,
        }
        # Insert before the + placeholder
        controls = self.device_list.controls
        placeholder_idx = next((i for i, c in enumerate(controls)
                                if getattr(c, "data", None) == "__add_device__"), len(controls))
        controls.insert(placeholder_idx, cell)
        try: self.page.update()
        except: pass

        # Kick off initial ping for local devices
        if is_local:
            threading.Thread(target=self._ping_custom, args=(key,), daemon=True).start()

    def _ping_custom(self, key):
        """Simple HTTP ping for custom local devices."""
        info = self.custom_devices.get(key, {})
        url = info.get("url", "")
        c = self.cards.get(key)
        if not c or not url: return
        try:
            r = requests.get(url, timeout=2.0)
            online = r.status_code < 500
        except:
            online = False
        if c:
            c["status"].value = "ONLINE" if online else "OFFLINE"
            c["status"].color = "cyan" if online else "red"
            c["_glow_state"] = "on" if online else "offline"
            c["glow"].border = ft.border.all(2, "#2b2b3b" if online else "#5a0000")
            c["glow"].bgcolor = "#0a1a1a" if online else "#1a0505"
            try: c["glow"].update(); c["status"].update()
            except: pass

    def _remove_custom_card(self, key):
        """Remove a custom device card."""
        c = self.cards.get(key)
        if not c: return
        name = c["name_label"].value
        def _confirm(_):
            dlg.open = False
            self.page.update()
            cell = c.get("cell")
            if cell and cell in self.device_list.controls:
                self.device_list.controls.remove(cell)
            self.cards.pop(key, None)
            self.custom_devices.pop(key, None)
            self.custom_names.pop(key, None)
            self.save_cache()
            self.log(f"Removed custom device '{name}'")
            try: self.page.update()
            except: pass
        def _cancel(_):
            dlg.open = False
            self.page.update()
        dlg = ft.AlertDialog(
            title=ft.Text("Remove device?"),
            content=ft.Text(f"Remove '{name}'?", size=13),
            actions=[
                ft.ElevatedButton("Remove", bgcolor="red900", color="white", on_click=_confirm),
                ft.TextButton("Cancel", on_click=_cancel),
            ]
        )
        self.page.overlay.append(dlg)
        dlg.open = True
        self.page.update()

    def _snapshot_device(self, ip):
        """Capture current state of a single device. Returns a state dict keyed ready for scene data."""
        c = self.cards.get(ip)
        if not c: return None
        dev_type = self.device_types.get(ip, "wled")
        state = {
            "on":   c["switch"].value,
            "bri":  self.individual_brightness.get(ip, 128),
            "type": dev_type,
            "preset": None,
            "color": self.mh_last_rgb.get(ip) if dev_type != "wled" else None,
            "mh_pattern": self.mh_mode.get(ip, {}).get("pattern"),
            "mh_speed":   self.mh_mode.get(ip, {}).get("speed", 10),
        }
        if dev_type == "wled":
            fx_val = c.get("fx_label") and c["fx_label"].value
            state["fx_name"] = fx_val or ""
            state["ps"] = self.active_preset.get(ip, -1)
        return state

    def edit_scene(self, idx):
        """Open a popup to add/remove/re-snapshot devices in an existing scene."""
        scene = self.scenes[idx] if idx < len(self.scenes) else None
        if not scene: return

        scene_data = scene["data"]  # cid -> state dict
        # Build list of all known devices with their inclusion state
        # Each row: (ip, cid, display_name, included)
        rows_data = []
        for ip, c in self.cards.items():
            cid = self.card_ids.get(ip)
            if not cid: continue
            name = c["name_label"].value or ip
            included = cid in scene_data
            rows_data.append([ip, cid, name, included])
        rows_data.sort(key=lambda x: x[2])  # sort by name

        # Build checkbox rows
        checks = {}   # cid -> ft.Checkbox
        def _build_rows():
            result = []
            for ip, cid, name, included in rows_data:
                cb = ft.Checkbox(value=included, active_color="cyan",
                    on_change=lambda e, c=cid: None)  # handled on save
                checks[cid] = cb
                def _snap(_, i=ip, c=cid, n=name):
                    snap = self._snapshot_device(i)
                    if snap:
                        scene_data[c] = snap
                        self.save_cache()
                        self.log(f"[Scene] Re-snapped '{n}' in '{scene['name']}'", color="cyan")
                snap_btn = ft.IconButton(
                    ft.Icons.REFRESH, icon_size=12, icon_color="grey500",
                    tooltip=f"Re-snapshot current state of {name}",
                    padding=0, on_click=_snap,
                )
                result.append(
                    ft.Row([
                        cb,
                        ft.Text(name, size=12, expand=True),
                        snap_btn,
                    ], spacing=6, vertical_alignment=ft.CrossAxisAlignment.CENTER)
                )
            return result

        def _save(_):
            # Apply checkbox changes to scene_data
            for ip, cid, name, was_included in rows_data:
                now_included = checks[cid].value
                if now_included and cid not in scene_data:
                    # Newly added — snapshot current state
                    snap = self._snapshot_device(ip)
                    if snap:
                        scene_data[cid] = snap
                        self.log(f"[Scene] Added '{name}' to '{scene['name']}'")
                elif not now_included and cid in scene_data:
                    # Removed
                    del scene_data[cid]
                    self.log(f"[Scene] Removed '{name}' from '{scene['name']}'")
            scene["data"] = scene_data
            self.save_cache()
            dlg.open = False
            self.page.update()
            self.log(f"[Scene] '{scene['name']}' updated — {len(scene_data)} devices", color="green400")

        def _cancel(_):
            dlg.open = False
            self.page.update()

        dlg = ft.AlertDialog(
            title=ft.Text(f"Edit Scene: {scene['name']}", color="#00f2ff"),
            content=ft.Container(
                width=360,
                height=400,
                content=ft.Column(
                    _build_rows(),
                    scroll=ft.ScrollMode.ADAPTIVE,
                    spacing=4,
                ),
            ),
            actions=[
                ft.ElevatedButton("Save", bgcolor="cyan", color="black", on_click=_save),
                ft.TextButton("Cancel", on_click=_cancel),
            ]
        )
        self.page.overlay.append(dlg)
        dlg.open = True
        self.page.update()

    def record_scene(self, idx):
        """Snapshot current state of all devices into scene slot."""
        snapshot = {}
        for ip in self.cards:
            cid = self.card_ids.get(ip)
            if not cid: continue
            state = self._snapshot_device(ip)
            if state:
                snapshot[cid] = state

        def _ask_name():
            field = ft.TextField(
                value=f"Scene {idx+1}", autofocus=True,
                border_color="cyan", width=280,
                on_submit=lambda e: _save(e))
            def _save(_):
                name = field.value.strip() or f"Scene {idx+1}"
                self.scenes[idx] = {"name": name, "data": snapshot}
                self.save_cache()
                dlg.open = False
                self.page.update()
                self._refresh_scene_btn(idx)
                self.log(f"[Scene] Recorded '{name}' ({len(snapshot)} devices)")
            def _cancel(_):
                dlg.open = False
                self.page.update()
            dlg = ft.AlertDialog(
                title=ft.Text("Name this scene"),
                content=ft.Column([
                    ft.Text(f"Capturing state of {len(snapshot)} devices.", size=12, color="grey400"),
                    field,
                ], tight=True, spacing=10),
                actions=[
                    ft.ElevatedButton("Save", bgcolor="cyan", color="black", on_click=_save),
                    ft.TextButton("Cancel", on_click=_cancel),
                ]
            )
            self.page.overlay.append(dlg)
            dlg.open = True
            self.page.update()

        _ask_name()

    def activate_scene(self, idx):
        """Restore all devices to the state saved in this scene."""
        scene = self.scenes[idx] if idx < len(self.scenes) else None
        if not scene:
            return
        self.log(f"[Scene] Activating '{scene['name']}'...")
        # Reset old active scene border then set new one (refs is a list — one per layout row)
        old = self.active_scene_idx
        self.active_scene_idx = idx
        if old is not None and old != idx and old in self.scene_btn_refs:
            for ref, _ in self.scene_btn_refs[old]:
                try:
                    ref.border = ft.border.all(1, "#2b2b3b")
                    ref.update()
                except: pass

        # Show LOADING... on button immediately
        if idx in self.scene_btn_refs:
            for ref, name_text in self.scene_btn_refs[idx]:
                try:
                    name_text.value = "LOADING..."
                    name_text.color = "grey400"
                    ref.update()
                except: pass

                
        def _apply():
            try:
                scene_name = scene["name"]

                # ----------------------------
                # Settings (tune these)
                # ----------------------------
                max_rounds = 10         # more rounds = more certainty (still fast)
                round_sleep = 1.5         # seconds between rounds
                tol_bri = 8             # brightness tolerance (0-255), ~8 ≈ 3%

                pending = {}            # ip -> scene state dict (ON and OFF targets)
                resend_count = {}       # ip -> resend attempts (debug)

                # ----------------------------
                # Small helpers
                # ----------------------------
                def _dev_name(ip):
                    c = self.cards.get(ip, {})
                    nl = c.get("name_label")
                    return nl.value if nl else ip

                def _target_on(st):
                    return bool(st.get("on", True))

                def _target_bri(st):
                    return max(1, min(255, int(st.get("bri", 128))))

                def _is_online(ip):
                    c = self.cards.get(ip)
                    return bool(c) and c.get("_glow_state") != "offline"

                def _current_on(ip):
                    c = self.cards.get(ip)
                    sw = c.get("switch") if c else None
                    return sw.value if sw else None

                def _current_bri(ip):
                    return self.individual_brightness.get(ip)

                def _bri_close(cur, target):
                    if cur is None:
                        return False
                    return abs(int(cur) - int(target)) <= tol_bri

                
                def _looks_done(ip, st):
                    if not _is_online(ip):
                        return False

                    want_on = _target_on(st)
                    cur_on = _current_on(ip)

                    if want_on is False:
                        return cur_on is False

                    if cur_on is not True:
                        return False

                    return _bri_close(_current_bri(ip), _target_bri(st))


                # ----------------------------
                # Dispatch helpers
                # ----------------------------
                def _dispatch_wled(ip, st, minimal=False):
                    """
                    WLED dispatch/resend.
                    - minimal=False: include preset if present
                    - minimal=True : only on+bri (avoid hammering presets)
                    """
                    payload = {"on": _target_on(st), "bri": _target_bri(st)}
                    if (not minimal) and st.get("ps", -1) > 0 and _target_on(st):
                        payload["ps"] = st["ps"]

                    threading.Thread(
                        target=self._safe_request,
                        kwargs={"m": "POST", "ip": ip, "d": payload, "scene": True},
                        daemon=True
                    ).start()

                def _dispatch_mh(ip, st):
                    """
                    MagicHome dispatch/resend.
                    OFF: power off
                    ON : power on + restore effect/color at target brightness
                    """
                    want_on = _target_on(st)
                    bri = _target_bri(st)
                    pat = st.get("mh_pattern")
                    spd = st.get("mh_speed", 10)
                    color = st.get("color") or (255, 255, 255)

                    def _send():
                        if not want_on:
                            self.send_magic_home_cmd(ip, [0x71, 0x24, 0x0F])
                            return

                        # Power ON first
                        self.send_magic_home_cmd(ip, [0x71, 0x23, 0x0F])

                        if pat is not None:
                            self.mh_mode[ip] = {"pattern": pat, "speed": spd}
                            self.send_magic_home_cmd(ip, [0x61, pat, spd, 0x0F])
                        else:
                            r, g, b = color
                            self.mh_last_rgb[ip] = (r, g, b)
                            ratio = bri / 255.0
                            self.send_magic_home_cmd(ip, [
                                0x31,
                                int(r * ratio), int(g * ratio), int(b * ratio),
                                0x00, 0xF0, 0x0F
                            ])

                    threading.Thread(target=_send, daemon=True).start()

                def _resend(ip, st, round_num):
                    """
                    Resend policy:
                      - only resend on rounds 2/4/6/8 to avoid spam
                      - OFF target: resend OFF if still ON
                      - ON target : resend ON (minimal payload after round>=4)
                    """
                    resend_count[ip] = resend_count.get(ip, 0) + 1

                    # If offline, don't spam; we'll fail it at the end as unknown
                    if not _is_online(ip):
                        return

                    want_on = _target_on(st)
                    cur_on = _current_on(ip)
                    dtype = st.get("type", "wled")

                    if not want_on:
                        # Target OFF: only resend if still ON
                        if cur_on is True:
                            self.dbg_unique(f"scene_retry:{ip}",
                                f"[Scene][RETRY] {_dev_name(ip)} OFF (round {round_num})",
                                color="orange400")
                            if dtype == "wled":
                                # minimal OFF command (on=False; bri is optional but harmless)
                                threading.Thread(
                                    target=self._safe_request,
                                    kwargs={"m": "POST", "ip": ip, "d": {"on": False}, "scene": True},
                                    daemon=True
                                ).start()
                            else:
                                _dispatch_mh(ip, st)
                        return

                    # Target ON
                    self.dbg_unique(f"scene_retry:{ip}",
                        f"[Scene][RETRY] {_dev_name(ip)} ON (round {round_num})",
                        color="orange400")

                    if dtype == "wled":
                        _dispatch_wled(ip, st, minimal=(round_num >= 4))
                    else:
                        _dispatch_mh(ip, st)

                # ----------------------------
                # Phase 1: DISPATCH (fast)
                # ----------------------------
                self.log(f"[Scene] Dispatching '{scene_name}' to devices...", color="grey400")

                for key, st in scene["data"].items():
                    # Resolve key → ip
                    ip = self.card_id_to_ip.get(key) if (len(key) == 36 and key.count("-") == 4) else key
                    if not ip or ip not in self.cards:
                        continue

                    c = self.cards[ip]
                    name = _dev_name(ip)
                    dtype = st.get("type", "wled")
                    want_on = _target_on(st)
                    bri = _target_bri(st)

                    # ✅ Track BOTH ON and OFF targets
                    pending[ip] = st

                    # Dispatch once
                    if dtype == "wled":
                        if want_on:
                            ps = st.get("ps", -1)
                            if ps > 0:
                                ps_name = self.preset_cache.get(ip, {}).get(str(ps), f"#{ps}")
                                self.log(f"[Scene] {name} → preset '{ps_name}'  {int((bri/255)*100)}%")
                            else:
                                self.log(f"[Scene] {name} → ON  {int((bri/255)*100)}%")
                        else:
                            self.log(f"[Scene] {name} → OFF", color="grey300")

                        _dispatch_wled(ip, st, minimal=False)

                    else:
                        if want_on:
                            pat = st.get("mh_pattern")
                            if pat is not None:
                                self.log(f"[Scene] {name} → MH effect", color="grey300")
                            else:
                                r, g, b = st.get("color") or (255, 255, 255)
                                cname = self._hex_to_name(f"#{r:02x}{g:02x}{b:02x}")
                                self.log(f"[Scene] {name} → color {cname}  {int((bri/255)*100)}%", color="grey300")
                        else:
                            self.log(f"[Scene] {name} → OFF", color="grey300")

                        _dispatch_mh(ip, st)

                self.dbg_unique("scene_dispatch",
                    f"[Scene][DBG] Dispatch complete: pending={len(pending)}",
                    color="grey500")

                # ----------------------------
                # Phase 2: RECONCILE (verify ON and OFF)
                # ----------------------------
                for r in range(1, max_rounds + 1):
                    if not pending:
                        break

                    self.dbg_unique("scene_round",
                        f"[Scene][DBG] Reconcile round {r}/{max_rounds}: pending={len(pending)}",
                        color="grey500")

                    for ip in list(pending.keys()):
                        st = pending[ip]

                        if _looks_done(ip, st):
                            self.dbg_unique(f"scene_ok:{ip}",
                                f"[Scene][OK] {_dev_name(ip)}",
                                color="green400")
                            pending.pop(ip, None)
                            continue

                        # Resend only on later rounds to avoid spamming
                        if r in (2, 4, 6, 8):
                            _resend(ip, st, r)

                    time.sleep(round_sleep)

                # ----------------------------
                # Final result + UI feedback
                # ----------------------------
                failed = list(pending.keys())

                # Persist cache once at end
                self.save_cache()

                if failed:
                    self.log(f"[Scene] '{scene_name}' — {len(failed)} device(s) failed / status unknown", color="red400")
                    self.dbg_unique("scene_failed_list",
                        f"[Scene][DBG] Failed/unknown: {', '.join(_dev_name(ip) for ip in failed)}",
                        color="red400")
                else:
                    self.log(f"[Scene] '{scene_name}' activated.", color="green400")

                # Button feedback (fixed: use scene_btn_refs[idx], not a typo)
                result_text = f"✗ {len(failed)} failed" if failed else "✓ Done"
                result_color = "red400" if failed else "green400"

                if idx in self.scene_btn_refs:
                    for ref, name_text in self.scene_btn_refs[idx]:
                        try:
                            name_text.value = result_text
                            name_text.color = result_color
                            ref.update()
                        except:
                            pass

                time.sleep(1.5)

                if idx in self.scene_btn_refs:
                    for ref, name_text in self.scene_btn_refs[idx]:
                        try:
                            name_text.value = scene_name
                            name_text.color = "#00f2ff"
                            ref.update()
                        except:
                            pass

            except Exception as e:
                # Never fail silently again
                import traceback
                self.log(f"[Scene][ERROR] _apply crashed: {e}", color="red400")
                self.log(traceback.format_exc(), color="red400")

                    
        threading.Thread(target=_apply, daemon=True).start()

    def clear_scene(self, idx):
        """Clear a scene slot with confirmation."""
        scene = self.scenes[idx] if idx < len(self.scenes) else None
        if not scene:
            return
        def _confirm(_):
            self.scenes[idx] = None
            self.save_cache()
            dlg.open = False
            self.page.update()
            self._refresh_scene_btn(idx)
            self.log(f"[Scene] Cleared slot {idx+1}")
        if self.active_scene_idx == idx:
            self.active_scene_idx = None
        def _cancel(_):
            dlg.open = False
            self.page.update()
        dlg = ft.AlertDialog(
            title=ft.Text("Clear scene?"),
            content=ft.Text(f"Remove '{scene['name']}'?", size=13),
            actions=[
                ft.ElevatedButton("Clear", bgcolor="red900", color="white", on_click=_confirm),
                ft.TextButton("Cancel", on_click=_cancel),
            ]
        )
        self.page.overlay.append(dlg)
        dlg.open = True
        self.page.update()

    def rename_scene(self, idx):
        """Rename an existing scene."""
        scene = self.scenes[idx] if idx < len(self.scenes) else None
        if not scene:
            return
        field = ft.TextField(value=scene["name"], autofocus=True,
            border_color="cyan", width=280,
            on_submit=lambda e: _save(e))
        def _save(_):
            name = field.value.strip() or scene["name"]
            self.scenes[idx]["name"] = name
            self.save_cache()
            dlg.open = False
            self.page.update()
            self._refresh_scene_btn(idx)
        def _cancel(_):
            dlg.open = False
            self.page.update()
        dlg = ft.AlertDialog(
            title=ft.Text("Rename scene"),
            content=field,
            actions=[
                ft.ElevatedButton("Save", bgcolor="cyan", color="black", on_click=_save),
                ft.TextButton("Cancel", on_click=_cancel),
            ]
        )
        self.page.overlay.append(dlg)
        dlg.open = True
        self.page.update()

    def confirm_remove_device(self, ip):
        """Ask user to confirm before removing a device card."""
        name = self.cards[ip]["name_label"].value if ip in self.cards else ip
        def _confirm(_):
            dlg.open = False
            self.page.update()
            self.remove_device(ip)
        def _cancel(_):
            dlg.open = False
            self.page.update()
        dlg = ft.AlertDialog(
            title=ft.Text("Remove Device?"),
            content=ft.Column([
                ft.Text(f"Remove '{name}' ({ip}) from the list?", size=13),
                ft.Text("The device will reappear if still on your network.", size=11, color="grey500"),
            ], tight=True, spacing=6),
            actions=[
                ft.ElevatedButton("Remove", bgcolor="red900", color="white", on_click=_confirm),
                ft.TextButton("Cancel", on_click=_cancel),
            ]
        )
        self.page.overlay.append(dlg)
        dlg.open = True
        self.page.update()

    def remove_device(self, ip):
        """Remove a device card from the UI and cache."""
        if ip not in self.cards:
            return
        name = self.cards[ip]["name_label"].value
        # Remove from device_list controls
        cell = self.cards[ip]["cell"]
        if cell in self.device_list.controls:
            self.device_list.controls.remove(cell)
        # Remove from all tracking dicts
        self.cards.pop(ip, None)
        self.devices.pop(ip, None)
        self.device_types.pop(ip, None)
        self.individual_brightness.pop(ip, None)
        self.custom_names.pop(ip, None)
        self.mh_mode.pop(ip, None)
        self.mh_last_rgb.pop(ip, None)
        self.effect_maps.pop(ip, None)
        self.fail_counts.pop(ip, None)
        self.locks.pop(ip, None)
        self.wled_devices.discard(ip)
        self.ledfx_devices.discard(ip)
        self.poll_counters.pop(ip, None)
        self.live_ips.discard(ip)
        self.save_cache()
        self.log(f"Removed device '{name}' ({ip})")
        try: self.page.update()
        except: pass

    def _default_display_name(self, name, dev_type):
        """Strip MAGICHOME- prefix and return a clean short ID."""
        n = name.split('.')[0].upper()
        if dev_type != "wled":
            # Strip common prefixes, keep the unique suffix
            for prefix in ["MAGICHOME-", "MAGIC-", "MH-"]:
                if n.startswith(prefix):
                    n = n[len(prefix):]
                    break
        return n

    def show_rename_dialog(self, ip):
        current = self.custom_names.get(ip, self.cards[ip]["name_label"].value)
        field = ft.TextField(value=current, autofocus=True, border_color="cyan",
                             hint_text="Enter display name", width=300,
                             on_submit=lambda e: do_save(e))
        def do_save(_):
            new_name = field.value.strip().upper()
            if new_name:
                self.custom_names[ip] = new_name
                self.cards[ip]["name_label"].value = new_name
                try: self.cards[ip]["name_label"].update()
                except: pass
                self.save_cache()
            dlg.open = False
            self.page.update()
        def do_cancel(_):
            dlg.open = False
            self.page.update()
        dlg = ft.AlertDialog(
            title=ft.Text("Rename Device"),
            content=ft.Column([
                ft.Text(f"IP: {ip}", size=11, color="grey500"),
                field,
            ], tight=True, spacing=10),
            actions=[
                ft.ElevatedButton("Save", bgcolor="cyan", color="black", on_click=do_save),
                ft.TextButton("Cancel", on_click=do_cancel),
            ]
        )
        self.page.overlay.append(dlg)
        dlg.open = True
        self.page.update()

    # ── Color + Preset popup helpers ─────────────────────────────────────────

    def show_anim_color_picker(self, target):
        """Color picker for title or border animation. target = 'title' or 'border'."""
        COLORS = [
            ("#FF0000","Red"),("#FF4400","Orange-Red"),("#FF8800","Orange"),
            ("#FFCC00","Amber"),("#FFFF00","Yellow"),("#AAFF00","Lime"),
            ("#00FF00","Green"),("#00FFAA","Mint"),("#00FFFF","Cyan"),
            ("#0088FF","Sky"),("#0000FF","Blue"),("#4400FF","Indigo"),
            ("#8800FF","Violet"),("#FF00FF","Magenta"),("#FF0088","Pink"),
            ("#FF88AA","Rose"),("#FFFFFF","White"),("#AAAAAA","Warm White"),
            ("#444444","Dim"),("#000000","Off"),
        ]
        def pick(hex_c, _dlg):
            _dlg.open = False
            self.page.update()
            if target == "title":
                self.title_color = hex_c
            else:
                self.border_color = hex_c
            self.save_cache()
        swatches = [
            ft.Container(width=44, height=44, border_radius=8, bgcolor=hex_c,
                border=ft.border.all(1,"#ffffff22"), tooltip=cname, ink=True,
                on_click=lambda _, h=hex_c, cn=cname: pick(h, dlg))
            for hex_c, cname in COLORS
        ]
        dlg = ft.AlertDialog(
            title=ft.Text(f"Pick color — {'Title' if target == 'title' else 'Card Borders'}"),
            content=ft.Container(
                content=ft.GridView(swatches, runs_count=5, max_extent=52, spacing=6, run_spacing=6),
                width=300, height=230,
            ),
            actions=[ft.TextButton("Cancel", on_click=lambda _: (setattr(dlg, "open", False), self.page.update()))]
        )
        self.page.overlay.append(dlg)
        dlg.open = True
        self.page.update()

    def show_anim_effect_picker(self, target):
        """Effect picker for title or border animation. target = 'title' or 'border'."""
        TITLE_EFFECTS = [
            ("rainbow_wave", "Rainbow Wave", "Hue scrolls across as a wave"),
            ("color_loop",   "Color Loop",   "Whole thing cycles through rainbow together"),
            ("breathing",    "Breathing",    "Slow fade in and out on chosen color"),
            ("strobe",       "Strobe",       "Rapid flash on chosen color"),
            ("solid",        "Solid",        "Static chosen color"),
        ]
        BORDER_EFFECTS = [
            ("color_loop",   "Color Loop",     "All cards cycle rainbow together"),
            ("rainbow_wave", "Rainbow Wave",   "Hue spreads across cards in list order"),
            ("wave_lr",      "Wave L→R",       "Wave travels left to right across columns"),
            ("wave_tb",      "Wave T→B",       "Wave travels top to bottom across rows"),
            ("diagonal",     "Diagonal",       "Wave travels diagonally across the grid"),
            ("chase",        "Chase",          "Snakes through grid in reading order"),
            ("orbit",        "Orbit / Ripple", "Ripple outward from center of grid"),
            ("breathing",    "Breathing",      "Slow fade in and out on chosen color"),
            ("strobe",       "Strobe",         "Rapid flash on chosen color"),
            ("solid",        "Solid",          "Static chosen color"),
        ]
        EFFECTS = TITLE_EFFECTS if target == "title" else BORDER_EFFECTS
        current = self.title_effect if target == "title" else self.border_effect
        def pick(effect_id, _dlg):
            _dlg.open = False
            self.page.update()
            if target == "title":
                self.title_effect = effect_id
            else:
                self.border_effect = effect_id
            self.save_cache()
        rows = [
            ft.ListTile(
                title=ft.Text(name, size=13, weight="bold" if eid == current else "normal"),
                subtitle=ft.Text(desc, size=10, color="grey400"),
                trailing=ft.Icon(ft.Icons.CHECK, color="cyan") if eid == current else None,
                on_click=lambda _, e=eid: pick(e, dlg),
            )
            for eid, name, desc in EFFECTS
        ]
        dlg = ft.AlertDialog(
            title=ft.Text(f"Effect — {'Title' if target == 'title' else 'Card Borders'}"),
            content=ft.Container(
                content=ft.Column(rows, scroll=ft.ScrollMode.AUTO, spacing=0),
                width=340, height=min(500, len(rows) * 64 + 20),
            ),
            actions=[ft.TextButton("Cancel", on_click=lambda _: (setattr(dlg, "open", False), self.page.update()))]
        )
        self.page.overlay.append(dlg)
        dlg.open = True
        self.page.update()

    def show_color_picker(self, ip):
        """Popup grid of common colors + send to device on tap."""
        COLORS = [
            ("#FF0000","Red"),("#FF4400","Orange-Red"),("#FF8800","Orange"),
            ("#FFCC00","Amber"),("#FFFF00","Yellow"),("#AAFF00","Lime"),
            ("#00FF00","Green"),("#00FFAA","Mint"),("#00FFFF","Cyan"),
            ("#0088FF","Sky"),("#0000FF","Blue"),("#4400FF","Indigo"),
            ("#8800FF","Violet"),("#FF00FF","Magenta"),("#FF0088","Pink"),
            ("#FF88AA","Rose"),("#FFFFFF","White"),("#AAAAAA","Warm White"),
            ("#444444","Dim"),("#000000","Off"),
        ]
        def send_color(hex_c, cname, _dlg):
            # Close immediately — send in background
            _dlg.open = False
            self.page.update()
            h = hex_c.lstrip("#")
            r, g, b = int(h[0:2],16), int(h[2:4],16), int(h[4:6],16)
            name = self.cards.get(ip, {}).get("name_label")
            card_name = name.value if name else ip
            if self.device_types.get(ip) == "wled":
                self.log(f"{card_name} — Color {cname} ({ip})", color="cyan")
                def _send():
                    ok = self._safe_request("POST", ip, {"seg":[{"col":[[r,g,b]]}],"on":True})
                    if ok:
                        self.page.run_task(self._async_update_visuals, ip, True)
                    else:
                        self.log(f"{card_name} — Color {cname} failed ({ip})", color="red400")
                threading.Thread(target=_send, daemon=True).start()
            else:
                # Store base color (unscaled) for future brightness math
                self.mh_last_rgb[ip] = (r, g, b)
                self.mh_mode[ip] = {"pattern": None}

                self.log(f"{card_name} — Color {cname} ({ip})", color="cyan")

                def _send_mh():
                    # Use current slider brightness (staged brightness) to scale the RGB
                    bri = int(self.individual_brightness.get(ip, 255))
                    bri = max(1, min(255, bri))
                    ratio = bri / 255.0

                    r1 = max(0, min(255, int(r * ratio)))
                    g1 = max(0, min(255, int(g * ratio)))
                    b1 = max(0, min(255, int(b * ratio)))

                    # Power ON first, then apply scaled color (prevents "ON resets to white" behavior)
                    self.send_magic_home_cmd(ip, [0x71, 0x23, 0x0F])
                    self.send_magic_home_cmd(ip, [0x31, r1, g1, b1, 0x00, 0xF0, 0x0F])

                    # Optional: confirm ping after a short delay
                    self._mh_confirm_ping(ip)

                threading.Thread(target=_send_mh, daemon=True).start()

        def close_dlg(d):
            d.open = False
            self.page.update()

        swatches = []
        for hex_c, cname in COLORS:
            swatches.append(
                ft.Container(
                    width=44, height=44, border_radius=8,
                    bgcolor=hex_c,
                    border=ft.border.all(1,"#ffffff22"),
                    tooltip=cname,
                    ink=True,
                    on_click=lambda _, h=hex_c, cn=cname: send_color(h, cn, dlg),
                )
            )
        dlg = ft.AlertDialog(
            title=ft.Text("Pick a Color"),
            content=ft.Container(
                content=ft.GridView(swatches, runs_count=5, max_extent=52, spacing=6, run_spacing=6),
                width=300, height=230,
            ),
            actions=[ft.TextButton("Cancel", on_click=lambda _: close_dlg(dlg))]
        )
        self.page.overlay.append(dlg)
        dlg.open = True
        self.page.update()

    def show_preset_picker(self, ip):
        """Popup list of WLED presets fetched from device."""
        def _load_and_show():
            try:
                raw = requests.get(f"http://{ip}/presets.json", timeout=6).json()
                presets = {k: v.get("n", f"Preset {k}") for k, v in raw.items()
                           if isinstance(v, dict) and v.get("n")}
                self.preset_cache[ip] = presets
            except:
                presets = self.preset_cache.get(ip, {})

            def activate(pid, _dlg):
                # Close dialog immediately — don't block UI on network call
                _dlg.open = False
                self.page.update()
                def _send():
                    ps_name = presets.get(str(pid), f"#{pid}")
                    name = self.cards.get(ip, {}).get("name_label")
                    card_name = name.value if name else ip
                    ok = self._safe_request("POST", ip, {"ps": int(pid)})
                    if ok:
                        self.log(f"[Preset] {card_name} → '{ps_name}'", color="cyan")
                        self.page.run_task(self._async_update_visuals, ip, True)
                    else:
                        self.log(f"[Preset] {card_name} ({ip}) → '{ps_name}' failed", color="red400")
                threading.Thread(target=_send, daemon=True).start()

            rows = [
                ft.ListTile(
                    title=ft.Text(pname, size=13),
                    trailing=ft.Text(f"#{pid}", size=10, color="grey500"),
                    on_click=lambda _, pid=pid: activate(pid, dlg),
                )
                for pid, pname in sorted(presets.items(), key=lambda x: int(x[0]))
            ] if presets else [ft.Text("No named presets found.", color="grey500", size=12)]

            def close_preset(d):
                d.open = False
                self.page.update()

            dlg = ft.AlertDialog(
                title=ft.Text("Select Preset"),
                content=ft.Container(
                    content=ft.Column(rows, scroll=ft.ScrollMode.AUTO, spacing=0),
                    width=320, height=min(400, len(rows)*52 + 20),
                ),
                actions=[ft.TextButton("Cancel", on_click=lambda _: close_preset(dlg))]
            )
            self.page.overlay.append(dlg)
            dlg.open = True
            self.page.update()

        threading.Thread(target=_load_and_show, daemon=True).start()

    def show_mh_modes(self, ip):
        """MagicHome mode popup — select effect, use brightness slider for speed."""
        MODES = [
            ("STATIC",          "Solid color — use color picker",  None),
            ("7-COLOR FADE",    "Smooth cycle through all colors", 0x25),
            ("RED FADE",        "Gradual red pulse",               0x26),
            ("GREEN FADE",      "Gradual green pulse",             0x27),
            ("BLUE FADE",       "Gradual blue pulse",              0x28),
            ("YELLOW FADE",     "Gradual yellow pulse",            0x29),
            ("CYAN FADE",       "Gradual cyan pulse",              0x2A),
            ("PURPLE FADE",     "Gradual purple pulse",            0x2B),
            ("WHITE FADE",      "Gradual white pulse",             0x2C),
            ("RED/GREEN FADE",  "Cross-fade red and green",        0x2D),
            ("RED/BLUE FADE",   "Cross-fade red and blue",         0x2E),
            ("GREEN/BLUE FADE", "Cross-fade green and blue",       0x2F),
            ("7-COLOR STROBE",  "Strobe through all colors",       0x30),
            ("RED STROBE",      "Red strobe flash",                0x31),
            ("GREEN STROBE",    "Green strobe flash",              0x32),
            ("BLUE STROBE",     "Blue strobe flash",               0x33),
            ("YELLOW STROBE",   "Yellow strobe flash",             0x34),
            ("CYAN STROBE",     "Cyan strobe flash",               0x35),
            ("PURPLE STROBE",   "Purple strobe flash",             0x36),
            ("WHITE STROBE",    "White strobe flash",              0x37),
            ("7-COLOR JUMP",    "Jump between colors",             0x38),
        ]
        SPEED_STEPS = [1, 3, 6, 10, 14, 20, 26, 31]

        def send_mode(pattern, _dlg, effect_label=""):
            # Use current brightness slider position as initial speed
            bri = self.individual_brightness.get(ip, 128)
            idx = 7 - min(7, int((bri - 1) * 8 / 255))
            spd_byte = SPEED_STEPS[idx]
            _cname = self.cards.get(ip, {}).get("name_label")
            _cn = _cname.value if _cname else ip
            if pattern is None:
                self.mh_mode[ip] = {"pattern": None}
                self.send_magic_home_cmd(ip, [0x71, 0x23, 0x0F])
                self.log(f"{_cn} — Effect: STATIC ({ip})", color="cyan")
                self._mh_confirm_ping(ip)
                if ip in self.cards:
                    self.cards[ip]["bri_text"].value = f"{int((bri/255)*100)}%"
                    try: self.cards[ip]["bri_text"].update()
                    except: pass
            else:
                self.mh_mode[ip] = {"pattern": pattern, "speed": spd_byte}
                self.send_magic_home_cmd(ip, [0x61, pattern, spd_byte, 0x0F])
                self.log(f"{_cn} — Effect: {effect_label} ({ip})", color="cyan")
                self._mh_confirm_ping(ip)
                if ip in self.cards:
                    self.cards[ip]["bri_text"].value = "SPD"
                    try: self.cards[ip]["bri_text"].update()
                    except: pass
            _dlg.open = False
            self.page.update()

        def close_mh(d):
            d.open = False
            self.page.update()

        dlg = ft.AlertDialog(
            title=ft.Text("MagicHome Modes"),
            content=ft.Container(
                width=320,
                content=ft.Column([
                    ft.Text("Use brightness slider to control speed after selecting an effect.",
                        size=10, color="grey500", italic=True),
                    ft.Divider(height=4),
                    ft.Column([
                        ft.ListTile(
                            title=ft.Text(label, weight="bold", size=13),
                            subtitle=ft.Text(desc, size=10, color="grey400"),
                            dense=True,
                            on_click=lambda _, p=pat, lb=label: send_mode(p, dlg, lb),
                        ) for label, desc, pat in MODES
                    ], scroll=ft.ScrollMode.AUTO, height=360, spacing=0),
                ], spacing=4),
            ),
            actions=[ft.TextButton("Cancel", on_click=lambda _: close_mh(dlg))]
        )
        self.page.overlay.append(dlg)
        dlg.open = True
        self.page.update()

    # ── Card builder ──────────────────────────────────────────────────────────

    def add_device_card(self, name, ip, initial_online=True, dev_type="wled"):
        # Extract MAC suffix from device name (e.g. "MH-11461E" -> "11461E", "wled-abc123" -> "ABC123")
        mac = self._extract_mac(name, dev_type)
        # Check if this MAC belongs to a known card with a different IP
        if mac and mac in self.mac_to_ip:
            old_ip = self.mac_to_ip[mac]
            if old_ip != ip and old_ip in self.cards:
                self._reassign_ip(old_ip, ip, name)
                return  # card updated in place, no new card needed
        if ip in self.cards: return
        self.devices[ip], self.device_types[ip] = name, dev_type
        # Track MAC
        if mac:
            self.device_macs[ip] = mac
            self.mac_to_ip[mac] = ip
        # Assign stable UUID if not already known (persisted across sessions)
        if ip not in self.card_ids:
            cid = str(uuid.uuid4())
            self.card_ids[ip] = cid
            self.card_id_to_ip[cid] = ip
        else:
            self.card_id_to_ip[self.card_ids[ip]] = ip  # ensure reverse map is current
            # Register in unified poll loop
            # ppp should this be in the eles or outside it
            if dev_type in ("wled", "magichome"):
                self.wled_devices.add(ip)
            self.fail_counts.setdefault(ip, 0)
            self.locks.setdefault(ip, 0)

        display_name = self.custom_names.get(ip) or self.display_names.get(ip) or self._default_display_name(name, dev_type)
        is_wled = dev_type == "wled"

        # ── shared widgets ────────────────────────────────────────────────────
        type_tag = ft.Container(
            content=ft.Text("WLED" if is_wled else "MH", size=9, weight="bold", color="white"),
            bgcolor="blue900" if is_wled else "green900",
            padding=ft.padding.symmetric(3,5), border_radius=4,
            ink=is_wled,
            tooltip="Open Web UI" if is_wled else None,
            on_click=(lambda _, i=ip: [
                self.log(f"{self.cards.get(i,{}).get('name_label',type('',(),({}))()).value or i} — Web UI opened ({i})", color="grey400"),
                self.page.launch_url(f"http://{i}")
            ]) if is_wled else None,
        )
        status     = ft.Text("OFFLINE", size=12, color="red", weight="bold")
        fx_label   = ft.Text("---", size=11, color="#00ffff")
        info_text  = ft.Text("---", size=10, color="grey500")
        name_label = ft.Text(display_name, weight="bold", size=16)
        edit_btn   = ft.IconButton(ft.Icons.EDIT, icon_size=13, icon_color="grey500",
                         tooltip="Rename", on_click=lambda _, i=ip: self.show_rename_dialog(i))
        update_btn = ft.ElevatedButton("UPDATE", visible=False, bgcolor="yellow700", color="black",
                         style=ft.ButtonStyle(shape=ft.RoundedRectangleBorder(radius=5),
                         text_style=ft.TextStyle(size=10, weight=ft.FontWeight.BOLD)),
                         on_click=lambda _, i=ip: threading.Thread(target=self.push_ota_update, args=(i,), daemon=True).start())
        _live_icon = ft.Icon(ft.Icons.BOLT, size=11, color="#ff6600")
        _live_text = ft.Text("LIVE", size=9, weight="bold", color="#ff6600")
        live_badge = ft.Container(
            visible=False,
            tooltip="LedFx has control — click to release back to WLED",
            ink=True,
            border_radius=6,
            on_click=lambda _, i=ip: self.toggle_live_badge(i),
            bgcolor="#3a1a00",
            border=ft.border.all(1, "#ff6600"),
            padding=ft.padding.symmetric(horizontal=6, vertical=3),
            content=ft.Row([_live_icon, _live_text], spacing=3, tight=True),
        )
        power_switch = ft.Switch(value=False, active_color="cyan",
                         on_change=lambda e: self.toggle_light(ip, e.control.value))
        bri_slider = ft.Slider(
          min=1, max=255, value=128, expand=True, active_color="cyan",
          on_change_start=lambda e, i=ip: self._on_bri_start(i),
          on_change=lambda e, i=ip: self._on_bri_drag(i, e.control.value),
          on_change_end=lambda e, i=ip: self._on_bri_end(i, e.control.value),
        )
        bri_text   = ft.Text("50%", size=10, color="grey400", text_align="center")

        # ── color swatch button (rainbow gradient suggestion) ─────────────────
        color_btn = ft.Container(
            width=54, height=54, border_radius=10,
            gradient=ft.LinearGradient(
                begin=ft.alignment.top_left, end=ft.alignment.bottom_right,
                colors=["#FF0000","#FF8800","#FFFF00","#00FF00","#00FFFF","#0000FF","#FF00FF","#FF0000"],
            ),
            border=ft.border.all(2, "#ffffff33"),
            tooltip="Pick color",
            ink=True,
            on_click=lambda _, i=ip: self.show_color_picker(i),
            content=ft.Icon(ft.Icons.COLORIZE, size=20, color="#ffffff88"),
        )

        # ── preset / mode button ──────────────────────────────────────────────
        preset_label = ft.Text("PRESET", size=7, color="#00f2ff", weight="bold",
                               max_lines=2, overflow="ellipsis", text_align="center")
        if is_wled:
            action_btn = ft.Container(
                width=54, height=54, border_radius=10,
                bgcolor="#1a1a2e",
                border=ft.border.all(2, "#00f2ff44"),
                tooltip="Select preset",
                ink=True,
                on_click=lambda _, i=ip: self.show_preset_picker(i),
                content=ft.Column([
                    ft.Icon(ft.Icons.AUTO_AWESOME, size=16, color="#00f2ff"),
                    preset_label,
                ], horizontal_alignment="center", alignment="center", spacing=2),
            )
        else:
            preset_label = ft.Text("MODES", size=7, color="#00f2ff", weight="bold")
            action_btn = ft.Container(
                width=54, height=54, border_radius=10,
                bgcolor="#1a1a2e",
                border=ft.border.all(2, "#00f2ff44"),
                tooltip="Light modes",
                ink=True,
                on_click=lambda _, i=ip: self.show_mh_modes(i),
                content=ft.Column([
                    ft.Icon(ft.Icons.TUNE, size=16, color="#00f2ff"),
                    preset_label,
                ], horizontal_alignment="center", alignment="center", spacing=2),
            )

        # ── Vertical reboot + sanitize (WLED only) ───────────────────────────
        reboot_btn = ft.GestureDetector(
            visible=is_wled,
            on_tap=lambda _, i=ip: self.confirm_reboot(i),
            mouse_cursor=ft.MouseCursor.CLICK,
            content=ft.Container(
                width=48, height=18,
                border_radius=4,
                tooltip="Reboot device",
                bgcolor="#00000000",
                content=ft.Text(
                    "REBOOT", size=8, weight="bold",
                    color="red400",
                    overflow=ft.TextOverflow.VISIBLE,
                ),
            ),
        )

        sanitize_btn = ft.GestureDetector(
            visible=is_wled,
            on_tap=lambda _, i=ip: None if i in self.live_ips else self.confirm_sanitize(i),
            mouse_cursor=ft.MouseCursor.CLICK,
            content=ft.Container(
                width=48, height=18,
                border_radius=4,
                tooltip="Sanitize presets",
                bgcolor="#00000000",
                content=ft.Text(
                    "SANITIZE", size=8, weight="bold",
                    color="yellow700",
                    overflow=ft.TextOverflow.VISIBLE,
                ),
            ),
        )

        # Center column — REBOOT stacked above SANITIZE with small gap
        _center_col = ft.Column([reboot_btn, sanitize_btn],
            spacing=4, tight=True, visible=is_wled)

        # ── card layout ───────────────────────────────────────────────────────
        card = ft.Container(
            data=ip, bgcolor="#16161e", border_radius=12,
            padding=ft.padding.only(left=12, right=12, top=10, bottom=10),
            content=ft.Column([

                # ROW 1: NAME | tag | ✏ | ✕ | spacer | POWER label+switch
                ft.Row([
                    name_label, type_tag,
                    edit_btn,
                    ft.IconButton(ft.Icons.CLOSE, icon_size=13, icon_color="red400",
                        tooltip="Remove this device",
                        on_click=lambda _, i=ip: self.confirm_remove_device(i)),
                    ft.Container(expand=True),
                    ft.Column([
                        ft.Text("POWER", size=9, color="grey500", text_align="center"),
                        power_switch,
                    ], horizontal_alignment="center", spacing=0),
                ], vertical_alignment="center", spacing=4),

                # ROW 2: left=info block, center=reboot+sanitize, right=color+preset
                ft.Row([
                    ft.Column([
                        ft.Text(ip, size=11, color="grey500"),
                        info_text,
                        status,
                        update_btn,
                        live_badge,
                    ], spacing=2, expand=True),
                    _center_col,
                    ft.Row([color_btn, action_btn], spacing=8),
                ], vertical_alignment="center", spacing=6),

                # ROW 3: full-width slider
                bri_slider,

            ], spacing=6)
        )

        glow = ft.Container(content=card, border_radius=13,
            border=ft.border.all(2, "#2b2b3b"), bgcolor="#16161e", padding=2)

        # Only the drag handle is Draggable — not the whole card
        # This prevents sliders/switches from accidentally triggering drags
        feedback = ft.Container(
            content=ft.Text(display_name, color="white", size=13, weight="bold"),
            bgcolor="#00f2ff22", border_radius=8, padding=10,
            border=ft.border.all(1, "#00f2ff"))

        handle_draggable = ft.Draggable(
            group="cards", data=ip,
            content=ft.Container(
                content=ft.Icon(ft.Icons.DRAG_INDICATOR, size=20, color="grey500"),
                tooltip="Drag to reorder",
                padding=ft.padding.only(right=6, top=4, bottom=4),
                border_radius=6,
                ink=True,
            ),
            content_feedback=feedback,
        )

        # Register draggable uid -> ip for reliable drag resolution
        self.draggable_map[str(id(handle_draggable))] = ip

        # Overlay: handle on the left edge, card fills the rest
        card_with_handle = ft.Row([
            handle_draggable,
            ft.Container(content=glow, expand=True),
        ], spacing=0)

        drag_target = ft.DragTarget(
            group="cards", content=card_with_handle,
            on_accept=lambda e, tgt=ip: self.drag_card(self._parse_drag_src(e.data), tgt),
            on_will_accept=lambda e, src=ip: self._parse_drag_src(e.data) != src,
        )
        # Use current window width so newly discovered cards get the right column size
        try:
            _cur_w = self.page.window.width or 1200
        except AttributeError:
            _cur_w = getattr(self.page, 'window_width', 1200) or 1200
        _col_map = {1: 60, 2: 30, 3: 20, 4: 15, 5: 12}
        _cur_col = _col_map[self._cols_for_width(_cur_w)]
        cell = ft.Container(content=drag_target,
            col=_cur_col, data=ip)

        self.cards[ip] = {
            "card": card, "glow": glow, "cell": cell,
            "handle": handle_draggable,
            "status": status, "switch": power_switch,
            "fx_label": fx_label, "preset_label": preset_label,
            "name_label": name_label,
            "bri_slider": bri_slider, "bri_text": bri_text,
            "info_text": info_text, "update_btn": update_btn,
            "sanitize_btn": sanitize_btn, "reboot_btn": reboot_btn, "edit_btn": edit_btn,
            "color_btn": color_btn, "action_btn": action_btn,
            "live_badge": live_badge, "live_icon": _live_icon, "live_text": _live_text,
        }
        # Insert before the + placeholder so it always stays last
        controls = self.device_list.controls
        placeholder_idx = next((i for i, c in enumerate(controls)
                                if getattr(c, "data", None) == "__add_device__"), len(controls))
        controls.insert(placeholder_idx, cell)
        # Register device for unified polling — new devices start as WLED-controlled
        self.wled_devices.add(ip)
        # Trigger immediate ping so card shows real status right away
        threading.Thread(target=self._ping_device, args=(ip, True), daemon=True).start()
        self.page.update()

    def start_merge_mode(self, e):
        """Toggle merge mode on/off. While active, dropping a card onto another shows merge dialog."""
        self.merge_mode = not self.merge_mode
        if self.merge_mode:
            self._merge_btn_icon.color = "orange400"
            self._merge_btn_text.value = "CANCEL MERGE"
            self._merge_btn_text.color = "orange400"
            self.log("[Merge] Merge mode ON — drop a new card onto the old card to merge", color="orange400")
        else:
            self._merge_btn_icon.color = "grey400"
            self._merge_btn_text.value = "MERGE"
            self._merge_btn_text.color = "grey400"
            self.log("[Merge] Merge mode cancelled")
        try:
            self._merge_btn_icon.update()
            self._merge_btn_text.update()
        except: pass

    def _extract_mac(self, name, dev_type):
        """Extract 6-char MAC suffix from device name. Returns None if not parseable."""
        try:
            n = name.split('.')[0].upper()
            if dev_type != "wled":
                # MagicHome: "MH-11461E" -> "11461E"
                for prefix in ["MH-", "MAGICHOME-", "MAGIC-"]:
                    if n.startswith(prefix):
                        suffix = n[len(prefix):]
                        if len(suffix) >= 6:
                            return suffix[-6:]
            else:
                # WLED: "wled-abc123" -> "ABC123"
                if '-' in n:
                    suffix = n.split('-')[-1]
                    if len(suffix) >= 6:
                        return suffix[-6:].upper()
        except: pass
        return None

    def _reassign_ip(self, old_ip, new_ip, new_name):
        """Silently move a card from old_ip to new_ip — keeps UUID, custom name, scenes etc.
        Note: card controls still reference old_ip via closure — app restart applies new IP fully.
        """
        self.log(f"[Device] IP change detected — {old_ip} → {new_ip} ({new_name})", color="cyan")
        cid = self.card_ids.get(old_ip)
        mac = self.device_macs.get(old_ip)

        # Update all IP-keyed dicts
        for d in [self.devices, self.device_types, self.cards, self.fail_counts,
                  self.locks, self.individual_brightness, self.custom_names,
                  self.display_names, self.preset_cache, self.active_preset,
                  self.mh_mode, self.mh_last_rgb, self.card_ids, self.device_macs]:
            if old_ip in d:
                d[new_ip] = d.pop(old_ip)

        # Update reverse maps
        if cid:
            self.card_id_to_ip[cid] = new_ip
        if mac:
            self.mac_to_ip[mac] = new_ip

        # Update cell.data so drag/drop and card order still work
        c = self.cards.get(new_ip, {})
        if c.get("cell"):
            c["cell"].data = new_ip
            try: c["cell"].update()
            except: pass

        # Update name label and info text to reflect new IP
        if c.get("info_text"):
            try: c["info_text"].update()
            except: pass

        self.devices[new_ip] = new_name
        self.log(f"[Device] {new_name} → saved at new IP {new_ip} — restart app to fully apply", color="cyan")

        # Update LedFx virtual maps so poll loop finds the device at its new IP
        # Also clear the mDNS IP cache so House.local re-resolves fresh next poll
        vid = self.ledfx_ip_to_virtual.get(old_ip)
        if vid:
            self.ledfx_virtual_map[vid] = new_ip
            self.ledfx_ip_to_virtual[new_ip] = vid
            self.ledfx_ip_to_virtual.pop(old_ip, None)
            self.dbg(f"[Device] LedFx virtual map updated: {vid} → {new_ip}")
        # Move segment vids to new IP
        if old_ip in self.ledfx_segment_vids:
            self.ledfx_segment_vids[new_ip] = self.ledfx_segment_vids.pop(old_ip)
        # Clear cached mDNS resolutions that pointed to old IP
        stale_hosts = [h for h, resolved in self._ledfx_ip_cache.items() if resolved == old_ip]
        for h in stale_hosts:
            self._ledfx_ip_cache.pop(h, None)
            self.dbg(f"[Device] Cleared mDNS cache for {h} (was {old_ip})")

        self.save_cache()
        # Trigger immediate poll at new IP
        threading.Thread(target=self._ping_device, args=(new_ip, True), daemon=True).start()

    def _merge_cards(self, keep_ip, discard_ip):
        """Merge discard card into keep card — keep card gets discard's IP, UUID stays.
        Used when a device reappears with a new IP and no MAC match was possible.
        """
        if keep_ip not in self.cards or discard_ip not in self.cards:
            self.log(f"[Merge] Cannot merge — one or both cards not found", color="orange400")
            return
        self.log(f"[Merge] Merging: keeping card '{self.cards[keep_ip]['name_label'].value}', "
                 f"assigning IP {discard_ip}", color="cyan")
        # Remove the discard card from UI
        discard_cell = self.cards[discard_ip].get("cell")
        if discard_cell and discard_cell in self.device_list.controls:
            self.device_list.controls.remove(discard_cell)
        # Move discard's IP data to keep card
        self._reassign_ip(keep_ip, discard_ip, self.devices.get(discard_ip, discard_ip))
        # Clean up old keep_ip remnants
        for d in [self.devices, self.device_types, self.fail_counts, self.locks,
                  self.individual_brightness, self.custom_names, self.display_names,
                  self.preset_cache, self.active_preset, self.mh_mode, self.mh_last_rgb,
                  self.card_ids, self.device_macs]:
            d.pop(keep_ip, None)
        try: self.page.update()
        except: pass
        self.log(f"[Merge] Done — card now at {discard_ip}", color="green400")
        # Auto-exit merge mode after a successful merge
        self.merge_mode = False
        self._merge_btn_icon.color = "grey400"
        self._merge_btn_text.value = "MERGE"
        self._merge_btn_text.color = "grey400"
        try: self._merge_btn_icon.update(); self._merge_btn_text.update()
        except: pass
        self.save_cache()

    def push_ota_update(self, ip):
        """Silently download the correct WLED .bin from GitHub and OTA-flash it to the device."""
        c = self.cards.get(ip)
        if not c:
            return

        # Disable button and show progress during update
        c["update_btn"].disabled = True
        c["update_btn"].text = "UPDATING..."
        try: c["update_btn"].update()
        except: pass

        self._open_log()
        self.log(f"[OTA] Starting silent firmware update for {ip}...")

        try:
            # 1. Fetch latest release assets from GitHub
            resp = requests.get(GITHUB_RELEASES_URL, timeout=10)
            resp.raise_for_status()
            assets = resp.json().get("assets", [])

            # 2. Determine the device architecture from the stored info_text (e.g. "0.14.4 | esp32")
            arch_hint = ""
            info_val = c["info_text"].value.lower() if c["info_text"].value else ""
            if "esp32s3" in info_val:
                arch_hint = "esp32s3"
            elif "esp32s2" in info_val:
                arch_hint = "esp32s2"
            elif "esp32c3" in info_val:
                arch_hint = "esp32c3"
            elif "esp32" in info_val:
                arch_hint = "esp32"
            else:
                arch_hint = "esp8266"  # fallback

            self.log(f"[OTA] Detected architecture: {arch_hint}")

            # 3. Find the best matching .bin asset using exact arch matching.
            # WLED asset names look like: WLED_0.15.4_ESP32.bin, WLED_0.15.4_ESP32-C3.bin etc.
            # We normalise by stripping dashes so "ESP32-C3" -> "esp32c3",
            # then match exact tokens so "esp32" never hits "esp32c3"/"esp32s3" files.
            import re

            def _arch_matches(asset_name_lower, arch):
                normalised = asset_name_lower.replace("-", "")
                tokens = re.findall(r'esp\w+', normalised)
                return arch in tokens

            download_url, target_name = None, ""
            for asset in assets:
                name = asset["name"].lower()
                if name.endswith(".bin") and "bootloader" not in name and _arch_matches(name, arch_hint):
                    download_url, target_name = asset["browser_download_url"], asset["name"]
                    break

            if not download_url:
                # Fallback: pick any non-bootloader .bin (last resort)
                for asset in assets:
                    name = asset["name"].lower()
                    if name.endswith(".bin") and "bootloader" not in name:
                        download_url, target_name = asset["browser_download_url"], asset["name"]
                        break

            if not download_url:
                self.log(f"[OTA] ERROR: No suitable .bin asset found for {arch_hint}.", color="red400")
                return

            self.log(f"[OTA] Downloading: {target_name}")

            # 4. Download firmware binary into memory
            firmware_bytes = b""
            with requests.get(download_url, stream=True, timeout=60) as r:
                r.raise_for_status()
                total = int(r.headers.get("content-length", 0))
                downloaded = 0
                chunks = []
                for chunk in r.iter_content(chunk_size=256 * 1024):
                    chunks.append(chunk)
                    downloaded += len(chunk)
                    if total > 0:
                        pct = int((downloaded / total) * 100)
                        self.log(f"[OTA] Download: {pct}%")
                firmware_bytes = b"".join(chunks)

            self.log(f"[OTA] Download complete ({len(firmware_bytes)//1024} KB). Flashing {ip}...")

            # 5. POST the binary to the device's OTA endpoint
            flash_resp = requests.post(
                f"http://{ip}/update",
                files={"update": (target_name, firmware_bytes, "application/octet-stream")},
                timeout=120
            )

            if flash_resp.status_code == 200:
                self.log(f"[OTA] SUCCESS: {ip} flashed. Device is rebooting...", color="green400")
                # Wait for device to come back online then verify version
                self._verify_post_flash(ip, self.latest_release_ver)
                return  # Don't restore button — _verify_post_flash handles it
            else:
                self.log(f"[OTA] ERROR: Device returned HTTP {flash_resp.status_code}", color="red400")

        except Exception as ex:
            self.log(f"[OTA] FAILED for {ip}: {ex}", color="red400")
        finally:
            # Only reached on error paths (success returns early above)
            c["update_btn"].disabled = False
            c["update_btn"].text = "UPDATE"
            try: c["update_btn"].update()
            except: pass

    def _verify_post_flash(self, ip, expected_ver):
        """Poll the device until it comes back online after OTA reboot, then check version."""
        c = self.cards.get(ip)
        if not c:
            return
        self.log(f"[OTA] Waiting for {ip} to reboot...")
        # Give device time to start rebooting before we poll
        time.sleep(8)
        for attempt in range(15):
            try:
                r = requests.get(f"http://{ip}/json", timeout=4).json()
                ver = r.get("info", {}).get("ver", "")
                if ver:
                    if ver == expected_ver:
                        self.log(f"[OTA] Verified: {ip} is now running {ver}. Up to date!", color="green400")
                        c["update_btn"].visible = False
                        try: c["update_btn"].update()
                        except: pass
                    else:
                        self.log(f"[OTA] WARNING: {ip} reports v{ver}, expected v{expected_ver}.", color="orange400")
                        c["update_btn"].disabled = False
                        c["update_btn"].text = "UPDATE"
                        try: c["update_btn"].update()
                        except: pass
                    return
            except:
                pass
            self.log(f"[OTA] Device offline, retrying... ({attempt+1}/15)")
            time.sleep(4)
        self.log(f"[OTA] {ip} did not come back online after 60s. Check device manually.", color="red400")
        c["update_btn"].disabled = False
        c["update_btn"].text = "UPDATE"
        try: c["update_btn"].update()
        except: pass

    def _dim_hex(self, hex_color, brightness):
        """Scale a hex color by a brightness factor 0.0-1.0."""
        h = hex_color.lstrip("#")
        if len(h) != 6: return hex_color
        r = int(int(h[0:2], 16) * brightness)
        g = int(int(h[2:4], 16) * brightness)
        b = int(int(h[4:6], 16) * brightness)
        return "#{:02x}{:02x}{:02x}".format(r, g, b)

    def _hue_to_hex(self, h):
        """Convert hue 0-360 to a dim RGB hex colour suitable for a border glow."""
        import colorsys
        r, g, b = colorsys.hsv_to_rgb(h / 360.0, 0.85, 0.75)
        return "#{:02x}{:02x}{:02x}".format(int(r * 255), int(g * 255), int(b * 255))

    def rainbow_loop(self):
        """Animate title characters and card borders at ~10fps.
        Both title and borders support: rainbow_wave, color_loop, breathing, strobe, solid.
        """
        _title_hue  = 0.0
        _border_hue = 0.0
        while self.running:
            # If any slider is currently being dragged, pause animations briefly
            if getattr(self, '_dragging', None) and len(self._dragging) > 0:
                time.sleep(0.05)
                continue
            # ── Advance hues ──────────────────────────────────────────────────
            _title_hue  = (_title_hue  + self.title_speed)  % 360
            _border_hue = (_border_hue + self.border_speed) % 360
            self.rainbow_hue = _border_hue  # keep shared hue in sync for badge etc.

            # ── Border color ──────────────────────────────────────────────────
            ef = self.border_effect
            if ef == "color_loop":
                border_color = self._hue_to_hex(_border_hue)
            elif ef == "rainbow_wave":
                border_color = None  # handled per-card below
            elif ef == "solid":
                # Speed slider controls brightness — minimum 10% so border is always visible
                _bri = max(0.10, self.border_speed / 20.0)
                border_color = self._dim_hex(self.border_color, _bri)
            elif ef == "breathing":
                self._breath_border += 0.05 * self.border_speed / 4.0 * self._breath_border_dir
                if self._breath_border >= 1.0:
                    self._breath_border = 1.0; self._breath_border_dir = -1
                elif self._breath_border <= 0.10:
                    self._breath_border = 0.10; self._breath_border_dir = 1
                border_color = self._dim_hex(self.border_color, self._breath_border)
            elif ef == "strobe":
                self._strobe_border = not self._strobe_border
                border_color = self.border_color if self._strobe_border else "#000000"
            else:
                border_color = self._hue_to_hex(_border_hue)

            # Apply border to all ON/live cards with grid-position-aware effects
            # Build ordered list matching device_list visual order
            # Custom cards (web, exe) always join the effect — they have no on/off state
            # Offline WLED/MH cards stay red and are excluded
            _ordered = []
            for ctrl in self.device_list.controls:
                ip = getattr(ctrl, "data", None)
                if ip and ip in self.cards:
                    c = self.cards[ip]
                    if c.get("_is_custom") or c.get("_glow_state") == "on" or ip in self.live_ips:
                        _ordered.append((ip, c))
            _card_count = len(_ordered)
            _any = False

            if _card_count > 0:
                # Calculate grid dimensions from current window width
                try:
                    _win_w = self.page.window.width or 1200
                except: _win_w = 1200
                _cols = self._cols_for_width(_win_w)
                _rows = max(1, (_card_count + _cols - 1) // _cols)
                _cx = _cols / 2.0  # grid center col
                _cy = _rows / 2.0  # grid center row

                for _ci, (ip, c) in enumerate(_ordered):
                    if not self.running: break
                    _col = _ci % _cols
                    _row = _ci // _cols

                    ef = self.border_effect
                    if ef == "color_loop":
                        _c = border_color
                    elif ef == "solid":
                        _c = border_color
                    elif ef == "breathing":
                        _c = border_color
                    elif ef == "strobe":
                        _c = border_color
                    elif ef == "rainbow_wave":
                        # Original — hue spreads across card list order
                        _spread = 300 / max(_card_count - 1, 1)
                        _c = self._hue_to_hex((_border_hue + _ci * _spread) % 360)
                    elif ef == "wave_lr":
                        # Wave travels left to right — offset by column
                        _spread = 300 / max(_cols - 1, 1)
                        _c = self._hue_to_hex((_border_hue + _col * _spread) % 360)
                    elif ef == "wave_tb":
                        # Wave travels top to bottom — offset by row
                        _spread = 300 / max(_rows - 1, 1)
                        _c = self._hue_to_hex((_border_hue + _row * _spread) % 360)
                    elif ef == "diagonal":
                        # Diagonal wave — offset by col + row
                        _spread = 300 / max(_cols + _rows - 2, 1)
                        _c = self._hue_to_hex((_border_hue + (_col + _row) * _spread) % 360)
                    elif ef == "chase":
                        # Chase — snakes through grid in reading order
                        _spread = 300 / max(_card_count - 1, 1)
                        _c = self._hue_to_hex((_border_hue + _ci * _spread) % 360)
                    elif ef == "orbit":
                        # Ripple from center — offset by distance from grid center
                        import math
                        _dist = math.sqrt((_col - _cx) ** 2 + (_row - _cy) ** 2)
                        _max_dist = math.sqrt(_cx ** 2 + _cy ** 2)
                        _spread = 300 / max(_max_dist, 1)
                        _c = self._hue_to_hex((_border_hue + _dist * _spread) % 360)
                    else:
                        _c = self._hue_to_hex(_border_hue)

                    c["glow"].border = ft.border.all(2, _c)
                    _any = True

            if _any:
                try: self.device_list.update()
                except: pass

            # Animate active scene button border
            active = self.active_scene_idx
            if active is not None and active in self.scene_btn_refs:
                _sc = border_color if border_color else self._hue_to_hex(_border_hue)
                for ref, _ in self.scene_btn_refs[active]:
                    try:
                        ref.border = ft.border.all(1, _sc)
                        ref.update()
                    except: pass

            # ── Title animation ───────────────────────────────────────────────
            if hasattr(self, "_title_chars"):
                tef = self.title_effect
                _non_space = [c for c in self._title_chars if c.value != " "]
                _spread = 300 / max(len(_non_space) - 1, 1)
                if tef == "rainbow_wave":
                    _ni = 0
                    for _tc in self._title_chars:
                        if _tc.value == " ": continue
                        _tc.color = self._hue_to_hex((_title_hue + _ni * _spread) % 360)
                        _ni += 1
                elif tef == "color_loop":
                    _c = self._hue_to_hex(_title_hue)
                    for _tc in self._title_chars:
                        _tc.color = _c
                elif tef == "solid":
                    # Speed slider controls brightness — minimum 10% so text stays visible
                    _bri = max(0.10, self.title_speed / 20.0)
                    _c = self._dim_hex(self.title_color, _bri)
                    for _tc in self._title_chars:
                        _tc.color = _c
                elif tef == "breathing":
                    self._breath_title += 0.05 * self.title_speed / 4.0 * self._breath_title_dir
                    if self._breath_title >= 1.0:
                        self._breath_title = 1.0; self._breath_title_dir = -1
                    elif self._breath_title <= 0.10:
                        self._breath_title = 0.10; self._breath_title_dir = 1
                    _c = self._dim_hex(self.title_color, self._breath_title)
                    for _tc in self._title_chars:
                        _tc.color = _c
                elif tef == "strobe":
                    self._strobe_title = not self._strobe_title
                    _c = self.title_color if self._strobe_title else "#000000"
                    for _tc in self._title_chars:
                        _tc.color = _c
                try:
                    self.header.update()
                except: pass
            time.sleep(0.1)

    def unified_poll_loop(self):
        """Unified polling loop for both WLED and LedFx devices.
        - Polls WLED devices from wled_devices set with adaptive timing based on device count
        - Polls LedFx API every 3s when running to manage live state
        - Handles device mode transitions between WLED/LedFx control
        """
        _wled_round_start = time.time()
        _ledfx_last_poll = 0
        _offline_skip = {}
        _ledfx_poll_count = 0

        while self.running:
            current_time = time.time()

            # Handle window focus state
            if not self.is_focused:
                time.sleep(UNFOCUSED_PAUSE)
                continue

            # Calculate adaptive WLED polling interval based on device count
            device_count = len(self.wled_devices)
            wled_interval = WLED_BASE_INTERVAL + (device_count // 10) * WLED_SCALE_FACTOR
            wled_interval = min(wled_interval, WLED_MAX_INTERVAL)

            # Poll WLED devices if enough time has passed
            if current_time - _wled_round_start >= wled_interval:
                _wled_round_start = current_time
                polled_wled = []
                if self.wled_devices:
                    # Poll WLED devices sequentially with offline backoff
                    for ip in list(self.wled_devices):
                        if not self.running or not self.is_focused:
                            break

                        is_offline = self.cards.get(ip, {}).get("_glow_state") == "offline"
                        if is_offline:
                            _offline_skip[ip] = _offline_skip.get(ip, 0) + 1
                            if _offline_skip[ip] % 3 != 0:  # Poll offline devices every 3rd round
                                continue
                        else:
                            _offline_skip.pop(ip, None)

                        polled_wled.append((self.cards.get(ip, {}).get('name_label').value if self.cards.get(ip, {}).get('name_label') else ip))
                        self._ping_device(ip)
                    if polled_wled:
                      self.dbg_unique('wled_poll_summary', '[WLED Poll] Polled: ' + ', '.join(polled_wled) + ' (' + str(len(polled_wled)) + ')')    
                else:
                    
                    # No WLED devices to poll, short sleep
                    time.sleep(1)

            # Poll LedFx API if running and enough time has passed
            if self.ledfx_running and current_time - _ledfx_last_poll >= LEDFX_POLL_INTERVAL:
                _ledfx_last_poll = current_time
                _ledfx_poll_count += 1
                _debug = (_ledfx_poll_count == 1)

                try:
                    # Fetch devices and virtuals in parallel-ish — two quick calls
                    r_dev = requests.get("http://localhost:8888/api/devices", timeout=2)
                    r_virt = requests.get("http://localhost:8888/api/virtuals", timeout=2)

                    devices = r_dev.json().get("devices", {})
                    if isinstance(devices, list):
                        devices = {d["id"]: d for d in devices}

                    virtuals = r_virt.json().get("virtuals", {})
                    if isinstance(virtuals, list):
                        virtuals = {v["id"]: v for v in virtuals}

                    if _debug:
                        self.log(f"[LedFx Poll] Got {len(devices)} devices, {len(virtuals)} virtuals", color="grey500")

                    # Build device_id -> IP map from devices response
                    dev_id_to_ip = {}
                    for did, dev in devices.items():
                        hostname = dev.get("config", {}).get("ip_address", "")
                        if hostname:
                            ip = self._resolve_ledfx_ip(hostname)
                            if ip:
                                dev_id_to_ip[did] = ip

                    # Build ip -> active map from device virtuals
                    ledfx_active = {}  # ip -> True/False
                    for vid, v in virtuals.items():
                        is_device = v.get("is_device")
                        if not is_device: continue
                        active = v.get("active", False)
                        streaming = v.get("streaming", False)

                        # Use cache or resolve from dev_id_to_ip
                        device_ip = self.ledfx_virtual_map.get(vid)
                        if not device_ip:
                            device_ip = dev_id_to_ip.get(is_device)
                            if device_ip:
                                self.ledfx_virtual_map[vid] = device_ip
                                self.ledfx_ip_to_virtual[device_ip] = vid
                                if _debug:
                                    name = self.cards.get(device_ip, {}).get("name_label")
                                    card_name = name.value if name else device_ip
                                    self.log(f"[LedFx Poll] Mapped '{vid}' → {device_ip} ({card_name})  active={active}", color="grey500")
                            elif _debug:
                                dev_type = devices.get(is_device, {}).get("type", "wled")
                                if dev_type == "wled":
                                    self.log(f"[LedFx Poll] No IP for virtual '{vid}' (is_device={is_device})", color="orange400")

                        if device_ip:
                            # streaming=True means LedFx is sending data even if active=False
                            if device_ip not in ledfx_active or active or streaming:
                                ledfx_active[device_ip] = active or streaming
                            # Debug log for LedFx device poll, similar to WLED ping
                            config = v.get("config", {})
                            bri = config.get("brightness", "N/A")
                            effect_name = config.get("effect", {}).get("name", "N/A") if config.get("effect") else "N/A"
                            self._dbg_ledfx_poll(device_ip, vid, active, streaming, bri, effect_name)


                    try:
                      _names = []
                      for _ip in ledfx_active.keys():
                        _nl = self.cards.get(_ip, {}).get('name_label')
                        _names.append(_nl.value if _nl else _ip)
                      if _names:
                        self.dbg_unique('ledfx_poll_summary', '[LedFx Poll] Polled: ' + ', '.join(_names) + ' (' + str(len(_names)) + ')')
                    except:
                      pass

                    # Apply live state changes to cards
                    for ip, should_be_live in ledfx_active.items():
                        was_live = ip in self.live_ips
                        if should_be_live != was_live:
                            if should_be_live:
                                self._set_card_live(ip)
                            else:
                                self._set_card_unlive(ip, ping_delay=0)

                    # Check for devices that should be unlive but aren't in active map
                    for ip in list(self.live_ips):
                        if ip not in ledfx_active:
                            self._set_card_unlive(ip, ping_delay=0)

                except Exception as e:
                    if _debug:
                        self.log(f"[LedFx Poll] Error: {e}", color="orange400")

            # Sleep briefly to prevent tight loop
            time.sleep(0.1)

    def fetch_latest_release(self):
        try:
            resp = requests.get(GITHUB_RELEASES_URL, timeout=10)
            if resp.status_code == 200:
                self.latest_release_ver = resp.json().get("tag_name", "").replace("v", "")
                self.log(f"Latest WLED: {self.latest_release_ver}", color="cyan")
        except: pass
        self.refresh_all_statuses()

    async def async_update_status(self, ip, is_online, new_name=None, is_on=None, fx_name=None, current_bri=None, ver=None, arch=None, rssi=None, is_live=False):
        if ip in self.cards and self._is_locked(ip):
          now = time.time()
          last = self._last_defer_log.get(ip, 0)
          if now - last > 1.0:
            self._last_defer_log[ip] = now
            self.dbg(f"Status update deferred {ip} — user input in progress, avoiding mid-drag override", color="orange400")
          return
        if ip in self.cards and not self._is_locked(ip):
            c = self.cards[ip]
            if is_online:
                if c.get("_glow_state") == "offline":
                    display = c["name_label"].value or ip
                    self.log(f"[Device] {display} ({ip}) back ONLINE", color="green400")
                if new_name:
                    c["name_label"].value = new_name.upper()
                    self.display_names[ip] = new_name.upper()
                if is_on is not None:
                    _prev_sw = c["switch"].value
                    if is_on != _prev_sw:
                        self.dbg(f"Switch update {ip}: is_on={is_on} (was {_prev_sw})")
                    c["switch"].value = is_on
                
                # --- BRIGHTNESS SYNC LOGIC ---
                # Skip slider update for MH devices in preset mode —
                # the slider controls speed there, not brightness, and
                # the hardware bri response byte is meaningless in that context.
                is_mh_preset = (self.device_types.get(ip) != "wled" and
                                self.mh_mode.get(ip, {}).get("pattern") is not None)

                if not is_mh_preset:
                    if is_on is True and current_bri is not None:
                        # Device is ON: Hardware reality takes priority
                        self.individual_brightness[ip] = current_bri
                        c["bri_slider"].value = max(1, int(current_bri))
                        c["bri_text"].value = f"{int((current_bri/255)*100)}%"
                    
                    elif is_on is False:
                        # Device is OFF: Use our saved "Staged" value
                        saved_bri = self.individual_brightness.get(ip)
                        if saved_bri is not None:
                            c["bri_slider"].value = max(1, int(saved_bri))
                            c["bri_text"].value = f"{int((saved_bri/255)*100)}%"
                        else:
                            # Only fallback to Master if we have zero history for this IP
                            self.individual_brightness[ip] = self.current_master_bri
                            c["bri_slider"].value = max(1, int(self.current_master_bri))
                            c["bri_text"].value = f"{int((self.current_master_bri/255)*100)}%"
                
                if fx_name:
                    c["fx_label"].value = fx_name.upper()  # keep for arch detection
                    if "preset_label" in c:
                        # Truncate long names to fit the button
                        short = fx_name.upper()[:10] + ("…" if len(fx_name) > 10 else "")
                        c["preset_label"].value = short
                if ver:
                    c["info_text"].value = f"{ver} | {arch}"
                    if self.latest_release_ver:
                        if ver != self.latest_release_ver:
                            c["update_btn"].visible = True
                        else:
                            # Version matches — hide button even if it was shown before
                            c["update_btn"].visible = False
                
                # Live state is managed by ledfx_poll_loop — skip status updates for live cards
                if ip in self.live_ips:
                    pass  # don't overwrite live badge or glow state
                else:
                    # Only hide badge if LedFx is not running — if it is running,
                    # the grey badge should stay so user can re-activate from the card
                    if not self.ledfx_running:
                        c["live_badge"].visible = False
                    c["status"].value = f"ONLINE ({rssi}%)" if rssi else "ONLINE"
                    c["status"].color = "cyan"
                    c["status"].visible = True
                    # Glow state: ON=rainbow (handled by rainbow_loop), OFF=dim teal
                    if is_on is True:
                        c["glow"].bgcolor = "#0a1a1a"
                        c["_glow_state"] = "on"
                    elif is_on is False:
                        c["glow"].bgcolor = "#16161e"
                        c["glow"].border = ft.border.all(2, "#2b2b3b")
                        c["_glow_state"] = "off"
            else:
                if c.get("_glow_state") not in ("offline",) and ip not in self.live_ips:
                    display = c["name_label"].value or self.custom_names.get(ip) or ip
                    self.log(f"[Device] {display} ({ip}) went OFFLINE", color="red400")
                c["status"].value = "OFFLINE"
                c["status"].color = "red"
                c["status"].visible = True
                c["glow"].bgcolor = "#1a0505"
                c["glow"].border = ft.border.all(2, "#5a0000")
                c["_glow_state"] = "offline"
            
            try: 
                c["card"].update()
                c["glow"].update()
            except: 
                pass

    def _ping_device(self, ip, force_full=False):
        if self._is_locked(ip) and not force_full: return
        _card = self.cards.get(ip)
        _disp = (_card["name_label"].value if _card else None) or ip
        _last_error = None
        for _attempt in range(3):
            try:
                if self.device_types.get(ip) == "wled":
                    if ip not in self.effect_maps or force_full:
                        self.effect_maps[ip] = requests.get(f"http://{ip}/json/eff", timeout=1.5).json()
                    r = requests.get(f"http://{ip}/json", timeout=1.5).json()
                    s, i = r.get("state", {}), r.get("info", {})
                    f_id = s.get("seg", [{}])[0].get("fx", 0)
                    f_name = self.effect_maps[ip][f_id] if ip in self.effect_maps else "FX"
                    is_on = s.get("on", False)
                    self.active_preset[ip] = s.get("ps", -1)
                    _bri = s.get("bri")
                    _rssi = i.get("wifi", {}).get("signal")
                    _col = s.get("seg", [{}])[0].get("col", [[]])[0] if s.get("seg") else []
                    _col_hex = "#{:02x}{:02x}{:02x}".format(*_col[:3]) if len(_col) >= 3 else "?"
                    _col_name = self._hex_to_name(_col_hex)
                    _ping_card = self.cards.get(ip, {})
                    _ping_name = _ping_card.get("name_label")
                    _ping_cn = _ping_name.value if _ping_name else ip
                    _bri_pct = f"{int((_bri/255)*100)}%" if _bri is not None else "?"
                    _wled_live = s.get("live", False)
                    self._dbg_wled_ping(ip, _ping_cn, is_on, _bri, f_name, _col_name, _rssi, _wled_live)
                    # Save MAC from WLED info — more reliable than extracting from mDNS name
                    raw_mac = i.get("mac", "")
                    if raw_mac and ip not in self.device_macs:
                        mac_suffix = raw_mac[-6:].upper()
                        self.device_macs[ip] = mac_suffix
                        self.mac_to_ip[mac_suffix] = ip
                    if is_on:
                        self.individual_brightness[ip] = s.get("bri", 128)
                    self.page.run_task(self.async_update_status, ip, True, i.get("name"), is_on, f_name, s.get("bri"), i.get("ver"), i.get("arch"), i.get("wifi",{}).get("signal"))
                else:
                    # MagicHome Logic
                    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
                        s.settimeout(2.0); s.connect((ip, MAGIC_HOME_PORT))
                        s.sendall(bytes([0x81, 0x8a, 0x8b, 0x96]))
                        d = s.recv(14)

                        
                        # SUCCESS: we reached the device over TCP, so it is ONLINE (even if OFF)
                        self.fail_counts[ip] = 0

                        is_on      = d[2] == 0x23
                        pattern    = d[3]
                        speed_byte = d[5]
                        
                        # new magichome brightness fix
                        r, g, b    = d[6], d[7], d[8]
                        
                        _mh_col_hex = "#{:02x}{:02x}{:02x}".format(r, g, b)
                        _mh_col_name = self._hex_to_name(_mh_col_hex)

                        bri_raw    = max(r, g, b)
                        bri        = bri_raw  # for UI reporting in static color mode
                        
                        _mh_fx = "off"

                        if pattern == 0x61:
                            # Static color mode: device reports *scaled* RGB.
                            # Normalize back to an approximate full-brightness base color so future scaling can brighten.
                            if bri_raw > 0:
                                base_r = min(255, int(r * 255 / bri_raw))
                                base_g = min(255, int(g * 255 / bri_raw))
                                base_b = min(255, int(b * 255 / bri_raw))
                                self.mh_last_rgb[ip] = (base_r, base_g, base_b)
                            # else: keep previous base color (don’t overwrite with black)

                            self.mh_mode[ip] = {"pattern": None}
                        
                        elif is_on and 0x25 <= pattern <= 0x38:
                            delay = max(1, min(0x1f, speed_byte))
                            inv_spd = int((delay - 1) * 100 / (0x1f - 1))
                            spd_pct = 100 - inv_spd
                            self.mh_mode[ip] = {"pattern": pattern, "speed": speed_byte}
                            bri = int(spd_pct * 255 / 100)
                        if is_on:
                            self.individual_brightness[ip] = max(1, bri)
                        # Debug ping log — matches WLED format
                        _mh_card = self.cards.get(ip, {})
                        _mh_name = _mh_card.get("name_label")
                        _mh_cn   = _mh_name.value if _mh_name else ip
                        _mh_bri_pct = f"{int((bri/255)*100)}%" if bri else "?"
                        
                        # if is_on and pattern == 0x61:
                        #     _mh_col_hex = "#{:02x}{:02x}{:02x}".format(r, g, b)
                        #     _mh_fx = f"color={self._hex_to_name(_mh_col_hex)}"
                        # elif is_on and 0x25 <= pattern <= 0x38:
                        #     _mh_fx = f"effect=0x{pattern:02X} spd={_mh_bri_pct}"
                        # else:
                        #     _mh_fx = "off"
                        
                        # Describe device mode (static vs effect)
                        # Always define first
                        _mh_fx = "off"
                        if is_on and pattern == 0x61:
                            _mh_col_hex = "#{:02x}{:02x}{:02x}".format(r, g, b)
                            _mh_fx = f"color={self._hex_to_name(_mh_col_hex)}"
                        elif is_on and 0x25 <= pattern <= 0x38:
                            _mh_fx = f"effect=0x{pattern:02X} spd={_mh_bri_pct}"
                        
                        _mh_fx = f"color={_mh_col_name}({_mh_col_hex})"
                        
                        self.dbg_unique(f"mhping:{ip}", f"Ping {_mh_cn} ({ip}): on={is_on} bri={_mh_bri_pct} {_mh_fx}")
                        self.page.run_task(self.async_update_status,ip, True, is_on=is_on, current_bri=(max(1, bri) if is_on else None)
)                    
                
                self.fail_counts[ip] = 0
                return  # success
            except Exception as _e:
                _last_error = _e
                if _attempt < 2:
                    time.sleep(0.3)
        # All 3 attempts failed
        if not self.ledfx_running:
            already_offline = self.cards.get(ip, {}).get("_glow_state") == "offline"
            self.fail_counts[ip] = self.fail_counts.get(ip, 0) + 1
            if not already_offline:
                self.log(f"[Ping] {_disp} ({ip}) failed 3 attempts: {_last_error}", color="orange400")
            if self.fail_counts[ip] > 2:
                self.page.run_task(self.async_update_status, ip, False)
    def brightness_worker(self):
        while self.running:
            item = self.brightness_queue.get()
            if not item: break
            ip, bri = item
            if self.device_types.get(ip) == "wled":
                self._safe_request("POST", ip, {"bri": max(1, min(255, int(bri)))})
            else:
                mh = self.mh_mode.get(ip, {"pattern": None})
                if mh.get("pattern") is not None:
                    # Preset mode — store speed only, send on release via on_change_end
                    SPEED_STEPS = [1, 3, 6, 10, 14, 20, 26, 31]
                    idx = 7 - min(7, int((bri - 1) * 8 / 255))
                    spd_byte = SPEED_STEPS[idx]
                    self.mh_mode[ip]["speed"] = spd_byte
                else:
                    # Static mode — scale last known color by brightness ratio
                    r0, g0, b0 = self.mh_last_rgb.get(ip, (255, 255, 255))
                    ratio = bri / 255.0
                    r1 = max(0, min(255, int(r0 * ratio)))
                    g1 = max(0, min(255, int(g0 * ratio)))
                    b1 = max(0, min(255, int(b0 * ratio)))
                    self.send_magic_home_cmd(ip, [0x31, r1, g1, b1, 0x00, 0xF0, 0x0F])
            self.brightness_queue.task_done()

    def handle_individual_brightness(self, ip, val):
        # 1. Update memory and UI text/slider
        self.individual_brightness[ip] = int(val)
        self._lock_ui(ip, 1) # Lock briefly while dragging to keep UI stable
        
        c = self.cards[ip]
        mh = self.mh_mode.get(ip, {"pattern": None}) if self.device_types.get(ip) != "wled" else {}
        if mh.get("pattern") is not None:
            spd_display = int((val / 255) * 10) + 1
            c["bri_text"].value = f"SPD {spd_display}"
        else:
            c["bri_text"].value = f"{int((val/255)*100)}%"
        
        # If the light is OFF, flip the switch to ON automatically
        _was_off = c["switch"].value is False
        if _was_off:
            c["switch"].value = True
            _nm = c.get("name_label")
            self.log(f"{_nm.value if _nm else ip} — Power ON via slider ({ip})", color="cyan")
            # No immediate command to device during drag: final action happens on release.
            # For MH/WLED we only set UI state now, and actual brightness/power is applied
            # by handle_brightness_release() after the user releases the slider.
            # This prevents hammering ESP32 with intermediate updates.
            self._update_card_visuals(ip, True)

        try:
            c["bri_text"].update()
            c["switch"].update()
        except:
            pass

        # 3. WLED/MH: suppress all device commands while dragging; final command applies on release.
        #    This avoids repeated ESP32/WLED updates during rapid slider movement.

        # 4. WLED/MH final command is handled by handle_brightness_release().

    def handle_brightness_release(self, ip, val):
        """Called when brightness slider is released — log final value, save, send MH command."""
        c = self.cards.get(ip, {})
        name = c.get("name_label")
        card_name = name.value if name else ip
        mh_mode = self.mh_mode.get(ip, {"pattern": None})
        if mh_mode.get("pattern") is not None:
            SPEED_STEPS = [1, 3, 6, 10, 14, 20, 26, 31]
            idx = 7 - min(7, int((val - 1) * 8 / 255))
            spd_label = ["MAX","FAST","MED+","MED","MED-","SLOW","V.SLOW","MIN"][idx]
            self.log(f"{card_name} — Speed {spd_label} ({ip})", color="cyan")
        else:
            self.log(f"{card_name} — Brightness {int((val/255)*100)}% ({ip})", color="cyan")
        self.save_cache()  # persist final brightness value on release
        if self.device_types.get(ip) == "wled":
            self.brightness_queue.put((ip, val))
            return
        # MagicHome: send the single final command now that the user has stopped sliding.
        # This is the only hardware command for MH brightness — nothing is sent during drag.
        mh = self.mh_mode.get(ip, {"pattern": None})
        def _send_mh_release(i=ip, v=val, m=mh):
            if m.get("pattern") is not None:
                SPEED_STEPS = [1, 3, 6, 10, 14, 20, 26, 31]
                idx = 7 - min(7, int((v - 1) * 8 / 255))
                spd_byte = SPEED_STEPS[idx]
                self.mh_mode[i]["speed"] = spd_byte
                self.send_magic_home_cmd(i, [0x61, m["pattern"], spd_byte, 0x0F])
            else:
                r0, g0, b0 = self.mh_last_rgb.get(i, (255, 255, 255))
                ratio = v / 255.0
                r1 = max(0, min(255, int(r0 * ratio)))
                g1 = max(0, min(255, int(g0 * ratio)))
                b1 = max(0, min(255, int(b0 * ratio)))
                self.send_magic_home_cmd(i, [0x31, r1, g1, b1, 0x00, 0xF0, 0x0F])
        threading.Thread(target=_send_mh_release, daemon=True).start()

    # ── Smooth slider drag handlers (send brightness only on release) ──────────

    def _on_bri_start(self, ip):

        self._dragging.add(ip)

        self._pending_bri[ip] = int(self.individual_brightness.get(ip, 128))

        self._lock_ui(ip, 3)


    def _on_bri_drag(self, ip, val):

        v = int(val)

        self._pending_bri[ip] = v

        self.individual_brightness[ip] = v

        now = time.time()

        last = self._last_slider_ui.get(ip, 0)

        if now - last < 0.06:

            return

        self._last_slider_ui[ip] = now

        c = self.cards.get(ip)

        if not c or c.get("_is_custom"):

            return

        is_mh_preset = (self.device_types.get(ip) != "wled" and self.mh_mode.get(ip, {}).get("pattern") is not None)

        if is_mh_preset:

            spd_display = int((v / 255) * 10) + 1

            c["bri_text"].value = "SPD " + str(spd_display)

        else:

            c["bri_text"].value = str(int((v/255)*100)) + "%"

        try:

            c["bri_text"].update()

        except:

            pass


    def _on_bri_end(self, ip, val):

        self._dragging.discard(ip)

        v = int(val)

        self._pending_bri[ip] = v

        self.individual_brightness[ip] = v

        c = self.cards.get(ip)

        if not c or c.get("_is_custom"):

            return

        if c.get("switch") and c["switch"].value is False:

            c["switch"].value = True

            try:

                c["switch"].update()

            except:

                pass

        self.handle_brightness_release(ip, v)


    def handle_master_brightness(self, e):
        val = int(e.control.value)
        if self.brightness_debounce_timer: self.brightness_debounce_timer.cancel()
        self.brightness_debounce_timer = threading.Timer(0.1, self._commit_relative_brightness, args=[val])
        self.brightness_debounce_timer.start()

    def _commit_relative_brightness(self, new_master_val):
        delta = new_master_val - self.prev_master_bri
        self.current_master_bri = new_master_val 
        self.prev_master_bri = new_master_val
        
        for ip in self.cards:
            c = self.cards[ip]
            # Skip custom launcher cards — no brightness controls
            if c.get("_is_custom") or "bri_slider" not in c:
                continue
            # Skip MagicHome devices that are running a preset effect
            is_mh_preset = (self.device_types.get(ip) != "wled" and
                            self.mh_mode.get(ip, {}).get("pattern") is not None)
            if is_mh_preset:
                continue

            nb = max(1, min(255, self.individual_brightness.get(ip, 128) + delta))
            self.individual_brightness[ip] = nb

            c["bri_slider"].value = max(1, int(nb))
            c["bri_text"].value = f"{int((nb/255)*100)}%"

            try:
                c["bri_slider"].update()
                c["bri_text"].update()
            except: pass

            if c["switch"].value is True:
                self._lock_ui(ip)
                self.brightness_queue.put((ip, nb))
                
        self.save_cache() # Save master slider change and all staged individual levels

    def _lock_ui(self, ip, duration=3): self.locks[ip] = time.time() + duration
    def _is_locked(self, ip): return ip in self.locks and time.time() < self.locks[ip]
    
    def _apply_cache(self, c):
        """Apply a loaded cache dict to self. Shared by load_cache and backup recovery."""
        self.cached_data = c.get("devices", {})
        self.device_types = c.get("types", {})
        self.card_order = c.get("card_order", [])
        self.current_master_bri = c.get("master_bri", 128)
        self.prev_master_bri = self.current_master_bri
        self.ledfx_path = c.get("ledfx_path")
        self.ledfx_current_ver = c.get("ledfx_ver", "2.0.0")
        self.individual_brightness = c.get("individual_bri", {})
        self.custom_names = c.get("custom_names", {})
        self.display_names = c.get("display_names", {})
        self.custom_devices = c.get("custom_devices", {})
        self.card_ids = c.get("card_ids", {})
        self.card_id_to_ip = {cid: ip for ip, cid in self.card_ids.items()}
        self.device_macs = c.get("device_macs", {})
        self.mac_to_ip = {mac: ip for ip, mac in self.device_macs.items()}
        raw_scenes = c.get("scenes", [None, None, None, None])
        self.scenes = self._migrate_scenes(raw_scenes)
        while len(self.scenes) < 4:
            self.scenes.append(None)
        self._win_w = c.get("win_w", 1200)
        self._win_h = c.get("win_h", 800)
        self._win_max = c.get("win_max", False)
        self.title_effect  = c.get("title_effect",  "rainbow_wave")
        self.title_speed   = c.get("title_speed",   4.0)
        self.title_color   = c.get("title_color",   "#ff0000")
        self.border_effect = c.get("border_effect", "color_loop")
        self.border_speed  = c.get("border_speed",  4.0)
        self.border_color  = c.get("border_color",  "#ff0000")
        self.debug_on_open = c.get("debug_on_open", False)
        self.log_auto_open = c.get("log_auto_open", False)

        # Initialize unified polling device sets — only add actual WLED/MH devices, not custom launcher cards
        self.wled_devices = set()
        for ip in self.cached_data.keys():
            dt = self.device_types.get(ip, "wled")
            if dt in ("wled", "magichome"):
                self.wled_devices.add(ip)
        self.ledfx_devices = set()  # Populated dynamically when LedFx poll detects active devices
        self.poll_counters = {}  # ip -> consecutive poll count

    def load_cache(self):
        """Load cache from disk. On failure, tries backups from newest to oldest."""
        self._cache_load_warning = None  # will be logged after UI is ready

        if os.path.exists(CACHE_FILE):
            try:
                with open(CACHE_FILE, "r") as f:
                    c = json.load(f)
                self._apply_cache(c)
                return  # success
            except Exception as e:
                self._cache_load_warning = f"[Cache] Main cache corrupted ({e}) — trying backups..."

        # Try backups newest-first
        pattern = os.path.join(LOG_DIR, "wledcc_cache_backup_*.json")
        backups = sorted(glob.glob(pattern), reverse=True)
        for bak in backups:
            try:
                with open(bak, "r") as f:
                    c = json.load(f)
                self._apply_cache(c)
                bak_name = os.path.basename(bak)
                msg = self._cache_load_warning or "[Cache] Main cache missing —"
                self._cache_load_warning = f"{msg} loaded backup '{bak_name}'"
                return  # success from backup
            except:
                continue  # try next backup

        # Nothing worked — start fresh
        if self._cache_load_warning:
            self._cache_load_warning += " — all backups failed, starting fresh"
        self.cached_data = {}

    def save_cache(self):
        sd, st, dn = {}, {}, {}
        for ip in self.cards:
            if ip in self.devices:
                sd[ip] = self.devices[ip]
            elif ip in self.cached_data:
                sd[ip] = self.cached_data[ip]  # preserve last known name if not yet seen this session
            st[ip] = self.device_types.get(ip, "wled")
            if ip in self.display_names:
                dn[ip] = self.display_names[ip]
            # Ensure MAC is tracked for any card that has a name
            if ip not in self.device_macs:
                dev_name = self.devices.get(ip, "")
                mac = self._extract_mac(dev_name, self.device_types.get(ip, "wled"))
                if mac:
                    self.device_macs[ip] = mac
                    self.mac_to_ip[mac] = ip
        # Capture the actual visual order from device_list.controls
        card_order = [
            getattr(c, "data", None)
            for c in getattr(self, "device_list", None) and self.device_list.controls or []
            if getattr(c, "data", None) is not None
        ]
        data = {
            "devices": sd,
            "types": st,
            "card_order": card_order,
            "master_bri": self.current_master_bri,
            "ledfx_path": self.ledfx_path,
            "ledfx_ver": self.ledfx_current_ver,
            "individual_bri": self.individual_brightness,
            "custom_names": self.custom_names,
            "display_names": dn,
            "custom_devices": self.custom_devices,
            "card_ids": self.card_ids,
            "device_macs": self.device_macs,
            "scenes": self.scenes,
            "win_w":   getattr(self, '_win_w', 1200),
            "win_h":   getattr(self, '_win_h', 800),
            "win_max": getattr(self, '_win_max', False),
            "title_effect":  self.title_effect,
            "title_speed":   self.title_speed,
            "title_color":   self.title_color,
            "border_effect": self.border_effect,
            "border_speed":  self.border_speed,
            "border_color":  self.border_color,
            "debug_on_open": self.debug_on_open,
            "log_auto_open": self.log_auto_open,
        }
        try:
            # Write backup before overwriting main file
            ts = datetime.now().strftime("%Y%m%d_%H%M%S")
            bak_path = os.path.join(LOG_DIR, f"wledcc_cache_backup_{ts}.json")
            with open(bak_path, "w") as f:
                json.dump(data, f)
            # Rotate — keep only newest CACHE_BACKUP_MAX backups
            existing = sorted(glob.glob(os.path.join(LOG_DIR, "wledcc_cache_backup_*.json")))
            while len(existing) > CACHE_BACKUP_MAX:
                os.remove(existing.pop(0))
            # Now write main file
            with open(CACHE_FILE, "w") as f:
                json.dump(data, f)
        except:
            pass
    def on_refresh_click(self, e):
        self.refresh_btn.disabled = True
        self._refresh_icon.color = "cyan"
        self._refresh_text.value = "SCANNING..."
        self._refresh_text.color = "cyan"
        try: self.refresh_btn.update()
        except: pass
        threading.Thread(target=self.refresh_all_statuses, args=(True,), daemon=True).start()
        threading.Thread(target=self.rescan_devices, daemon=True).start()

    
    
    # ppp new scan
    def rescan_devices(self):
        """Discovery scan — Two 5-second passes for better reliability.
        Prints a full device report at the end showing online/offline/new status.
        """
        self.log("─" * 40)
        self.log("Starting dual-pass scan (10s total)...")
        found_mh_ips = set()
        known_ips_before = set(self.cards.keys())
        PASS_DURATION = 5  # 5 seconds per pass
        
        from zeroconf import Zeroconf, ServiceBrowser

        # Run two separate discovery passes
        for pass_idx in range(2):
            self.log(f"Scan pass {pass_idx + 1}/2...")
            
            # Ensure clean mDNS state for this pass
            try:
                if hasattr(self, 'browser') and self.browser:
                    self.browser.cancel()
                    self.browser = None
            except: pass

            try:
                if hasattr(self, 'zeroconf') and self.zeroconf:
                    self.zeroconf.close()
                    self.zeroconf = None
            except: pass

            self.zeroconf = Zeroconf()

            # Start WLED mDNS browser
            try:
                self.browser = ServiceBrowser(self.zeroconf, "_wled._tcp.local.", WLEDListener(self))
            except Exception as ex:
                self.log(f"[Scan] WLED mDNS error: {ex}", color="red400")

            # MagicHome broadcast loop
            try:
                s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
                s.setsockopt(socket.SOL_SOCKET, socket.SO_BROADCAST, 1)
                s.settimeout(0.5)
                deadline = time.time() + PASS_DURATION
                next_broadcast = 0
                
                while time.time() < deadline:
                    if time.time() >= next_broadcast:
                        s.sendto("HF-A11ASSISTHREAD".encode(), ('255.255.255.255', 48899))
                        next_broadcast = time.time() + 2 # Faster broadcast for short scan
                    try:
                        d, a = s.recvfrom(1024)
                        r = d.decode().split(',')
                        if len(r) >= 2:
                            mh_ip = r[0]
                            if mh_ip not in found_mh_ips:
                                found_mh_ips.add(mh_ip)
                                name = f"MH-{r[1][-6:]}"
                                is_new = mh_ip not in known_ips_before
                                tag = "NEW" if is_new else "ONLINE"
                                self.log(f"  ✓ {name} ({mh_ip})  [{tag}]", color="green400")
                                self.page.run_task(self.async_add, name, mh_ip, "magichome")
                    except: pass
                s.close()
            except Exception as ex:
                self.log(f"[Scan] MagicHome error: {ex}", color="red400")

            # Shut down mDNS browser for this pass
            try:
                if self.browser:
                    self.browser.cancel()
                    self.browser = None
                if self.zeroconf:
                    self.zeroconf.close()
                    self.zeroconf = None
            except: pass
            
            if pass_idx == 0:
                time.sleep(0.5) # Short breather between passes

        # Brief pause so heartbeat has time to update glow states on new devices
        time.sleep(1)

        # ── Device report (Runs once after both passes) ───────────────────────
        wled_online, wled_offline, wled_new = [], [], []
        mh_online, mh_offline, mh_new = [], [], []
        for ip, c in list(self.cards.items()):
            name = c["name_label"].value or ip
            is_new = ip not in known_ips_before
            dev_type = self.device_types.get(ip, "wled")
            if dev_type == "wled":
                state = c.get("_glow_state", "offline")
            else:
                state = "online" if ip in found_mh_ips else "offline"
            
            entry = (name, ip, is_new, state)
            if dev_type == "wled":
                if is_new:               wled_new.append(entry)
                elif state == "offline": wled_offline.append(entry)
                else:                    wled_online.append(entry)
            else:
                if is_new:               mh_new.append(entry)
                elif state == "offline": mh_offline.append(entry)
                else:                    mh_online.append(entry)

        self.log("─" * 40)
        self.log("DEVICE REPORT", color="white")
        if wled_online or wled_new:
            self.log(f"  WLED — ONLINE ({len(wled_online) + len(wled_new)}):")
            for name, ip, is_new, _ in wled_online + wled_new:
                tag = " [NEW]" if is_new else ""
                self.log(f"    ✓ {name} ({ip}){tag}", color="green400")
        if wled_offline:
            self.log(f"  WLED — OFFLINE ({len(wled_offline)}):")
            for name, ip, _, _ in wled_offline:
                self.log(f"    ✗ {name} ({ip})", color="red400")
        if mh_online or mh_new:
            self.log(f"  MagicHome — ONLINE ({len(mh_online) + len(mh_new)}):")
            for name, ip, is_new, _ in mh_online + mh_new:
                tag = " [NEW]" if is_new else ""
                self.log(f"    ✓ {name} ({ip}){tag}")
        if mh_offline:
            self.log(f"  MagicHome — OFFLINE ({len(mh_offline)}):")
            for name, ip, _, _ in mh_offline:
                self.log(f"    ✗ {name} ({ip})")
        
        total = len(self.cards)
        total_on = len(wled_online) + len(wled_new) + len(mh_online) + len(mh_new)
        total_off = len(wled_offline) + len(mh_offline)
        self.log(f"  Total: {total} devices — {total_on} online, {total_off} offline", color="white")
        self.log("─" * 40)

        # Re-enable refresh button
        self._refresh_icon.color = "grey400"
        self._refresh_text.value = "SCAN"
        self._refresh_text.color = "grey400"
        self.refresh_btn.disabled = False
        try: self.refresh_btn.update()
        except: pass
        self.save_cache()
    
    # ppp - new two time pass above
    # def rescan_devices(self):
        # """Discovery scan — 10 second window, MagicHome broadcast sent 3 times (every 3s).
        # Prints a full device report at the end showing online/offline/new status.
        # """
        # self.log("─" * 40)
        # self.log("Scanning for devices (30s)...")
        # found_mh_ips = set()
        # known_ips_before = set(self.cards.keys())
        # SCAN_DURATION = 30
        
        # #nonetype fix start
        # from zeroconf import Zeroconf, ServiceBrowser

        # # Ensure clean mDNS state
        # try:
            # if self.browser:
                # self.browser.cancel()
                # self.browser = None
        # except:
            # pass

        # try:
            # if self.zeroconf:
                # self.zeroconf.close()
                # self.zeroconf = None
        # except:
            # pass

        # self.zeroconf = Zeroconf()
        # #nonetype fix end

        # # Start WLED mDNS browser — runs for full scan duration
        # try:
            # if self.browser:
                # self.browser.cancel()
            # self.browser = ServiceBrowser(self.zeroconf, "_wled._tcp.local.", WLEDListener(self))
        # except Exception as ex:
            # self.log(f"[Scan] WLED mDNS error: {ex}", color="red400")

        # # MagicHome broadcast — runs concurrently for full scan duration
        # try:
            # s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
            # s.setsockopt(socket.SOL_SOCKET, socket.SO_BROADCAST, 1)
            # s.settimeout(0.5)
            # deadline = time.time() + 5 # ppp SCAN_DURATION
            # next_broadcast = 0
            # while time.time() < deadline:
                # if time.time() >= next_broadcast:
                    # s.sendto("HF-A11ASSISTHREAD".encode(), ('255.255.255.255', 48899))
                    # next_broadcast = time.time() + 5
                # try:
                    # d, a = s.recvfrom(1024)
                    # r = d.decode().split(',')
                    # if len(r) >= 2:
                        # mh_ip = r[0]
                        # if mh_ip not in found_mh_ips:
                            # found_mh_ips.add(mh_ip)
                            # name = f"MH-{r[1][-6:]}"
                            # is_new = mh_ip not in known_ips_before
                            # tag = "NEW" if is_new else "ONLINE"
                            # self.log(f"  ✓ {name} ({mh_ip})  [{tag}]", color="green400")
                            # self.page.run_task(self.async_add, name, mh_ip, "magichome")
                # except: pass
            # s.close()
        # except Exception as ex:
            # self.log(f"[Scan] MagicHome error: {ex}", color="red400")

        # # Shut down mDNS browser
        # try:
            # if self.browser:
                # self.browser.cancel()
                # self.browser = None
        # except: pass

        # # Brief pause so heartbeat has time to update glow states on new devices
        # time.sleep(1)

        # # ── Device report ─────────────────────────────────────────────────────
        # wled_online, wled_offline, wled_new = [], [], []
        # mh_online, mh_offline, mh_new = [], [], []
        # for ip, c in list(self.cards.items()):
            # name = c["name_label"].value or ip
            # is_new = ip not in known_ips_before
            # dev_type = self.device_types.get(ip, "wled")
            # if dev_type == "wled":
                # state = c.get("_glow_state", "offline")
            # else:
                # # MagicHome: online if found during this scan, offline otherwise
                # state = "online" if ip in found_mh_ips else "offline"
            # entry = (name, ip, is_new, state)
            # if dev_type == "wled":
                # if is_new:               wled_new.append(entry)
                # elif state == "offline": wled_offline.append(entry)
                # else:                    wled_online.append(entry)
            # else:
                # if is_new:               mh_new.append(entry)
                # elif state == "offline": mh_offline.append(entry)
                # else:                    mh_online.append(entry)

        # self.log("─" * 40)
        # self.log("DEVICE REPORT", color="white")
        # if wled_online or wled_new:
            # self.log(f"  WLED — ONLINE ({len(wled_online) + len(wled_new)}):")
            # for name, ip, is_new, _ in wled_online + wled_new:
                # tag = " [NEW]" if is_new else ""
                # self.log(f"    ✓ {name} ({ip}){tag}", color="green400")
        # if wled_offline:
            # self.log(f"  WLED — OFFLINE ({len(wled_offline)}):")
            # for name, ip, _, _ in wled_offline:
                # self.log(f"    ✗ {name} ({ip})", color="red400")
        # if mh_online or mh_new:
            # self.log(f"  MagicHome — ONLINE ({len(mh_online) + len(mh_new)}):")
            # for name, ip, is_new, _ in mh_online + mh_new:
                # tag = " [NEW]" if is_new else ""
                # self.log(f"    ✓ {name} ({ip}){tag}")
        # if mh_offline:
            # self.log(f"  MagicHome — OFFLINE ({len(mh_offline)}):")
            # for name, ip, _, _ in mh_offline:
                # self.log(f"    ✗ {name} ({ip})")
        # total = len(self.cards)
        # total_on = len(wled_online) + len(wled_new) + len(mh_online) + len(mh_new)
        # total_off = len(wled_offline) + len(mh_offline)
        # self.log(f"  Total: {total} devices — {total_on} online, {total_off} offline", color="white")
        # self.log("─" * 40)

        # # Re-enable refresh button
        # self._refresh_icon.color = "grey400"
        # self._refresh_text.value = "SCAN"
        # self._refresh_text.color = "grey400"
        # self.refresh_btn.disabled = False
        # try: self.refresh_btn.update()
        # except: pass
        # # Save cache after every scan — ensures json exists after first run
        # self.save_cache()

    def refresh_all_statuses(self, force_full=False):
        """Manual refresh — stagger pings 150ms apart so we don't flood the network.
        Skips live devices (LedFx has control) and custom cards (not pingable via WLED/MH protocol).
        """
        self.is_refreshing = True
        ips = [ip for ip in self.devices.keys()
               if ip not in self.live_ips
               and not self.cards.get(ip, {}).get("_is_custom")]
        threads = []
        for ip in ips:
            t = threading.Thread(target=self._ping_device, args=(ip, force_full), daemon=True)
            threads.append(t)
            t.start()
            time.sleep(0.15)
        for t in threads: t.join(timeout=8.0)
        self.is_refreshing = False
        # Button re-enabled by rescan_devices after full 30s discovery window

    def toggle_light(self, ip, value):
        name = self.cards.get(ip, {}).get("name_label")
        card_name = name.value if name else ip
        action = "ON" if value else "OFF"
        self.log(f"{card_name} — Power {action} ({ip})", color="cyan" if value else "grey400")
        self._lock_ui(ip, 5)
        # Pull the current staged brightness (it updates even when off)
        b = self.individual_brightness.get(ip, 128)
    
        if self.device_types.get(ip) == "wled":
            ok = self._safe_request("POST", ip, {"on": value, "bri": b})
            if ok: self.page.run_task(self._async_update_visuals, ip, value)
        else:
            # MagicHome: 0x23 is ON, 0x24 is OFF
            if value:
                mh = self.mh_mode.get(ip, {"pattern": None})
                if mh.get("pattern") is not None:
                    # Was in a preset effect — restore it
                    self.send_magic_home_cmd(ip, [0x61, mh["pattern"], mh.get("speed", 0x1A), 0x0F])
                else:
                    # Was in static color — restore last known color at current brightness
                    r0, g0, b0 = self.mh_last_rgb.get(ip, (255, 255, 255))
                    ratio = b / 255.0
                    self.send_magic_home_cmd(ip, [0x31,
                        int(r0 * ratio), int(g0 * ratio), int(b0 * ratio),
                        0x00, 0xF0, 0x0F])
            self.send_magic_home_cmd(ip, [0x71, 0x23 if value else 0x24, 0x0f])
            # Immediate visual feedback — don't wait for confirm ping
            self._update_card_visuals(ip, value)
            # Confirm via ping after 1s
            self._mh_confirm_ping(ip)
    def broadcast_power(self, s):
        """Dispatch power command to all devices simultaneously, then reconcile with
        a ping loop and resend on even rounds — same pattern as activate_scene.
        """
        status_text = "ON" if s else "OFF"

        # Collect IPs — do NOT pre-set switch values; let the poll loop
        # update card state from real device confirmations (same as scenes).
        ips = []
        for ip, c in self.cards.items():
            if c.get("_is_custom") or "switch" not in c: continue
            ips.append(ip)

        self.log(f"[Broadcast] Dispatching POWER {status_text} to {len(ips)} device(s)...", color="grey400")

        def _worker():
            try:
                max_rounds  = 10
                round_sleep = 1.5
                resend_count = {}

                # ---- helpers ------------------------------------------------
                def _dev_name(ip):
                    c = self.cards.get(ip, {})
                    nl = c.get("name_label")
                    return nl.value if nl else ip

                def _is_online(ip):
                    c = self.cards.get(ip)
                    return bool(c) and c.get("_glow_state") != "offline"

                def _current_on(ip):
                    c = self.cards.get(ip)
                    sw = c.get("switch") if c else None
                    return sw.value if sw else None

                def _looks_done(ip):
                    if not _is_online(ip):
                        return False
                    return _current_on(ip) == s

                def _dispatch_wled(ip):
                    bri = self.individual_brightness.get(ip, 128)
                    threading.Thread(
                        target=self._safe_request,
                        kwargs={"m": "POST", "ip": ip, "d": {"on": s, "bri": bri}, "scene": True},
                        daemon=True
                    ).start()

                def _dispatch_mh(ip):
                    bri = self.individual_brightness.get(ip, 128)
                    def _send():
                        try:
                            if s:
                                mh = self.mh_mode.get(ip, {"pattern": None})
                                if mh.get("pattern") is not None:
                                    self.send_magic_home_cmd(ip, [0x61, mh["pattern"], mh.get("speed", 0x1A), 0x0F])
                                else:
                                    r0, g0, b0 = self.mh_last_rgb.get(ip, (255, 255, 255))
                                    ratio = bri / 255.0
                                    self.send_magic_home_cmd(ip, [0x31,
                                        int(r0*ratio), int(g0*ratio), int(b0*ratio), 0x00, 0xF0, 0x0F])
                            self.send_magic_home_cmd(ip, [0x71, 0x23 if s else 0x24, 0x0F])
                            # MH has no poll loop — update card visuals after confirmed send
                            self._update_card_visuals(ip, s)
                        except Exception as _e:
                            self.dbg(f"[Broadcast] MH {ip} send error: {_e}", color="orange400")
                    threading.Thread(target=_send, daemon=True).start()

                def _resend(ip, round_num):
                    resend_count[ip] = resend_count.get(ip, 0) + 1
                    if not _is_online(ip):
                        return
                    self.dbg_unique(f"bcast_retry:{ip}",
                        f"[Broadcast][RETRY] {_dev_name(ip)} {status_text} (round {round_num})",
                        color="orange400")
                    if self.device_types.get(ip) == "wled":
                        _dispatch_wled(ip)
                    else:
                        _dispatch_mh(ip)

                # ---- Phase 1: dispatch all simultaneously --------------------
                pending = {}
                for ip in ips:
                    pending[ip] = True
                    dtype = self.device_types.get(ip, "wled")
                    self.log(f"[Broadcast] {_dev_name(ip)} → {status_text}",
                             color="cyan" if s else "grey400")
                    if dtype == "wled":
                        _dispatch_wled(ip)
                    else:
                        _dispatch_mh(ip)

                self.dbg_unique("bcast_dispatch",
                    f"[Broadcast][DBG] Dispatch complete: pending={len(pending)}",
                    color="grey500")

                # ---- Phase 2: reconcile -------------------------------------
                for r in range(1, max_rounds + 1):
                    if not pending:
                        break

                    self.dbg_unique("bcast_round",
                        f"[Broadcast][DBG] Reconcile round {r}/{max_rounds}: pending={len(pending)}",
                        color="grey500")

                    for ip in list(pending.keys()):
                        if _looks_done(ip):
                            self.dbg_unique(f"bcast_ok:{ip}",
                                f"[Broadcast][OK] {_dev_name(ip)}",
                                color="green400")
                            pending.pop(ip, None)
                            continue
                        if r in (2, 4, 6, 8):
                            _resend(ip, r)

                    time.sleep(round_sleep)

                # ---- Phase 3: report ----------------------------------------
                failed = list(pending.keys())
                if failed:
                    self.log(
                        f"[Broadcast] POWER {status_text} — {len(failed)} device(s) failed / status unknown",
                        color="red400")
                    self.dbg_unique("bcast_failed_list",
                        f"[Broadcast][DBG] Failed/unknown: {', '.join(_dev_name(ip) for ip in failed)}",
                        color="red400")
                else:
                    self.log(f"[Broadcast] POWER {status_text} — all devices confirmed.", color="green400")

            except Exception as e:
                import traceback
                self.log(f"[Broadcast][ERROR] worker crashed: {e}", color="red400")
                self.log(traceback.format_exc(), color="red400")

        threading.Thread(target=_worker, daemon=True).start()
    def move_card(self, ip, direction):
        def _find_idx(ip):
            for i, c in enumerate(self.device_list.controls):
                if getattr(c, "data", None) == ip: return i
            return -1
        idx = _find_idx(ip)
        ni = idx + direction
        if 0 <= ni < len(self.device_list.controls):
            self.device_list.controls.insert(ni, self.device_list.controls.pop(idx))
            self.page.update(); self.save_cache()

    def _parse_drag_src(self, data):
        """Resolve drag source to an IP address.
        Flet passes e.data as JSON like {"src_id":"_760","x":...} not the draggable.data value.
        We match src_id against the uid of each registered handle draggable.
        """
        if not data:
            return data
        s = str(data).strip()
        if not s.startswith("{"):
            return s  # already a plain IP string
        try:
            import json as _json
            obj = _json.loads(s)
            src_id = obj.get("src_id", "")
            # Match against uid of each handle draggable
            for ip, c in self.cards.items():
                handle = c.get("handle")
                if handle is None:
                    continue
                uid = getattr(handle, "uid", None)
                if uid and (str(uid) == src_id or src_id == f"_{uid}" or
                            src_id.lstrip("_") == str(uid).lstrip("_")):
                    return ip
            # Fallback: try python id() map
            for ip, c in self.cards.items():
                handle = c.get("handle")
                if handle and str(id(handle)) == src_id:
                    return ip
        except: pass
        self.log(f"[Drag] WARNING: could not resolve src_id '{s}' to an IP", color="orange400")
        return s

    def _set_card_live(self, ip):
        """Lock a WLED card into live mode — freeze controls, show orange badge."""
        c = self.cards.get(ip)
        if not c or c.get("_is_custom"): return
        if ip in self.live_ips: return  # already live
        self.dbg(f"_set_card_live: {ip}", color="orange400")
        self.live_ips.add(ip)
        # Move device from WLED control to LedFx control
        #ppp disabled to try pinging live devices to get remote status changes
        #also need to change set_card_unlive if adding this back in
        #self.wled_devices.discard(ip)
        self.ledfx_devices.add(ip)
        self.poll_counters.pop(ip, None)  # Reset poll counter for new mode
        # Lock and dim all effect/color controls uniformly
        # Buttons use .disabled; GestureDetector (sanitize) uses opacity + live_ips guard in on_tap
        for key in ("color_btn", "action_btn"):
            ctrl = c.get(key)
            if ctrl:
                ctrl.disabled = True
                ctrl.opacity = 0.3
                try: ctrl.update()
                except: pass
        san = c.get("sanitize_btn")
        if san and san.content:
            san.content.opacity = 0.3
            try: san.update()
            except: pass
        c["live_badge"].visible = True
        c["live_icon"].color = "#ff6600"
        c["live_text"].color = "#ff6600"
        c["live_badge"].bgcolor = "#3a1a00"
        c["live_badge"].border = ft.border.all(1, "#ff6600")
        c["live_badge"].tooltip = "LedFx has control — click to release back to WLED"
        c["status"].visible = False
        c["glow"].bgcolor = "#0a1a1a"
        c["glow"].border = ft.border.all(2, self._hue_to_hex(self.rainbow_hue))
        c["_glow_state"] = "on"  # rainbow_loop animates this just like a powered-on card
        try: c["card"].update(); c["glow"].update()
        except: pass

    def _set_card_unlive(self, ip, ping_delay=1.5, manual=False):
        """Release a WLED card from live mode — restore controls, show grey badge.
        Badge visibility is managed globally by ledfx_monitor_loop (show on start,
        hide on stop). This method only changes badge colour and unlocks controls.
        manual param retained for call-site compatibility but no longer changes behaviour.
        """
        c = self.cards.get(ip)
        if not c or c.get("_is_custom"): return
        if ip not in self.live_ips: return  # already unlive
        self.dbg(f"_set_card_unlive: {ip}", color="cyan")
        self.live_ips.discard(ip)
        self.lor2_ips.discard(ip)
        # Move device from LedFx control back to WLED control
        self.ledfx_devices.discard(ip)
        #ppp disabled to try pinging live devices to get remote status changes
        #also need to change set_card_live if adding this back in
        #self.wled_devices.add(ip)
        self.poll_counters.pop(ip, None)  # Reset poll counter for new mode
        # Restore all effect/color controls uniformly
        for key in ("color_btn", "action_btn"):
            ctrl = c.get(key)
            if ctrl:
                ctrl.disabled = False
                ctrl.opacity = 1.0
                try: ctrl.update()
                except: pass
        san = c.get("sanitize_btn")
        if san and san.content:
            san.content.opacity = 1.0
            try: san.update()
            except: pass
        c["live_badge"].visible = True
        c["live_icon"].color = "grey500"
        c["live_text"].color = "grey500"
        c["live_badge"].bgcolor = "#1e1e2a"
        c["live_badge"].border = ft.border.all(1, "grey700")
        c["live_badge"].tooltip = "Click to re-activate in LedFx"
        c["status"].value = "CHECKING..."
        c["status"].color = "grey500"
        c["status"].visible = True
        c["glow"].bgcolor = "#16161e"
        c["glow"].border = ft.border.all(2, "#2b2b3b")
        c["_glow_state"] = "off"
        try: c["card"].update(); c["glow"].update()
        except: pass
        def _delayed_ping(delay=ping_delay):
            time.sleep(delay)
            self.dbg(f"Delayed post-live ping firing for {ip}")
            self._ping_device(ip, True)
        threading.Thread(target=_delayed_ping, daemon=True).start()

    async def _apply_live_ui(self, ledfx_on):
        """Apply or clear live state on all WLED cards at once (e.g. LedFx start/stop)."""
        idx = 0
        for ip, c in list(self.cards.items()):
            if c.get("_is_custom") or self.device_types.get(ip) != "wled":
                continue
            if ledfx_on:
                self._set_card_live(ip)
            else:
                self._set_card_unlive(ip, ping_delay=1.5 + idx * 0.3)
                idx += 1

    def toggle_live_badge(self, ip):
        """Toggle LedFx control for a device.
        Orange badge (live) → click releases to WLED, badge goes grey.
        Grey badge (manually released) → click re-activates in LedFx, badge goes orange.
        """
        c = self.cards.get(ip)
        if not c: return
        name = c["name_label"].value if c.get("name_label") else ip
        vid = self.ledfx_ip_to_virtual.get(ip)

        if ip in self.live_ips:
            # ── Release: deactivate main virtual AND all segment virtuals ─────
            seg_vids = self.ledfx_segment_vids.get(ip, [])
            all_vids = ([vid] if vid else []) + seg_vids
            if all_vids:
                self._releasing_ips.add(ip)  # block poll loop from re-locking during release
                def _deactivate(vids=all_vids, device_ip=ip):
                    failed = []
                    # Send all deactivations concurrently
                    def _one(v):
                        try:
                            r = requests.put(f"http://localhost:8888/api/virtuals/{v}",
                                             json={"active": False}, timeout=3)
                            if r.status_code not in (200, 204):
                                failed.append(v)
                        except Exception:
                            failed.append(v)
                    threads = [threading.Thread(target=_one, args=(v,), daemon=True) for v in vids]
                    for t in threads: t.start()
                    for t in threads: t.join(timeout=4)
                    self._releasing_ips.discard(device_ip)
                    if failed:
                        self.log(f"[Live] {name} — could not deactivate: {failed}", color="orange400")
                    else:
                        self.log(f"[Live] {name} — released from LedFx ({len(vids)} virtual(s)), click grey badge to re-activate", color="cyan")
                threading.Thread(target=_deactivate, daemon=True).start()
            else:
                self.log(f"[Live] {name} — no LedFx virtual mapped, releasing locally", color="orange400")
            self._set_card_unlive(ip, manual=True)

        else:
            # ── Re-activate: tell LedFx to turn virtual AND segment virtuals back on ──
            seg_vids = self.ledfx_segment_vids.get(ip, [])
            all_vids = ([vid] if vid else []) + seg_vids
            if all_vids:
                def _reactivate(vids=all_vids):
                    def _one(v):
                        try:
                            requests.put(f"http://localhost:8888/api/virtuals/{v}",
                                         json={"active": True}, timeout=3)
                        except: pass
                    threads = [threading.Thread(target=_one, args=(v,), daemon=True) for v in vids]
                    for t in threads: t.start()
                    for t in threads: t.join(timeout=4)
                    self.log(f"[Live] {name} — re-activated in LedFx ({len(vids)} virtual(s))", color="orange400")
                threading.Thread(target=_reactivate, daemon=True).start()
            else:
                self.log(f"[Live] {name} — no LedFx virtual mapped", color="orange400")

    def drag_card(self, src_ip, tgt_ip):
        """Swap src card to position of tgt card, or offer merge if both cards exist."""
        self.log(f"[Drag] drop: {src_ip} → {tgt_ip}")
        if src_ip == tgt_ip:
            self.log("[Drag] same card, ignoring")
            return

        # Only offer merge dialog when merge mode is active
        if not self.merge_mode:
            controls = self.device_list.controls
            def _find(ip):
                for i, c in enumerate(controls):
                    if getattr(c, "data", None) == ip: return i
                return -1
            src_idx = _find(src_ip)
            tgt_idx = _find(tgt_ip)
            if src_idx == -1 or tgt_idx == -1: return
            controls.insert(tgt_idx, controls.pop(src_idx))
            self.page.update()
            self.save_cache()
            return

        src_name = self.cards.get(src_ip, {}).get("name_label")
        tgt_name = self.cards.get(tgt_ip, {}).get("name_label")
        src_label = src_name.value if src_name else src_ip
        tgt_label = tgt_name.value if tgt_name else tgt_ip

        def _do_reorder():
            controls = self.device_list.controls
            def _find(ip):
                for i, c in enumerate(controls):
                    if getattr(c, "data", None) == ip: return i
                return -1
            src_idx = _find(src_ip)
            tgt_idx = _find(tgt_ip)
            if src_idx == -1 or tgt_idx == -1: return
            controls.insert(tgt_idx, controls.pop(src_idx))
            self.page.update()
            self.save_cache()

        def _do_merge(_):
            dlg.open = False
            self.page.update()
            # src is the new/unwanted card, tgt is the old card to keep
            self._merge_cards(keep_ip=tgt_ip, discard_ip=src_ip)

        def _do_reorder_from_dlg(_):
            dlg.open = False
            self.page.update()
            _do_reorder()

        def _cancel(_):
            dlg.open = False
            self.page.update()

        dlg = ft.AlertDialog(
            title=ft.Text("Reorder or Merge?", color="cyan"),
            content=ft.Column([
                ft.Text(f"You dropped '{src_label}' onto '{tgt_label}'.", size=13),
                ft.Divider(),
                ft.Text("REORDER — move the card to this position (normal drag behaviour)", size=12, color="grey400"),
                ft.Text(f"MERGE — '{tgt_label}' keeps its name and scenes. '{src_label}' card is removed.", size=12, color="grey400"),
            ], tight=True, spacing=8, width=400),
            actions=[
                ft.ElevatedButton("REORDER", bgcolor="#1e1e2a", color="white", on_click=_do_reorder_from_dlg),
                ft.ElevatedButton("MERGE", bgcolor="cyan", color="black", on_click=_do_merge),
                ft.TextButton("Cancel", on_click=_cancel),
            ]
        )
        self.page.overlay.append(dlg)
        dlg.open = True
        self.page.update()

    def discover_magic_home(self):
        """Legacy stub — discovery now handled by rescan_devices."""
        pass

    MH_CMD_INTERVAL = 1.0   # minimum seconds between commands to the same MH device

    def send_magic_home_cmd(self, ip, cmd):
        if not self.running: return
        # Rate limit — enforce minimum gap between commands to the same device.
        # MagicHome controllers crash/reboot when flooded with back-to-back TCP commands.
        now = time.time()
        last = self.mh_last_cmd.get(ip, 0)
        gap = self.MH_CMD_INTERVAL - (now - last)
        if gap > 0:
            time.sleep(gap)
        self.mh_last_cmd[ip] = time.time()
        try:
            with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
                s.settimeout(3); s.connect((ip, MAGIC_HOME_PORT)); s.sendall(bytes(cmd + [sum(cmd) & 0xFF]))
        except: pass

    def confirm_reboot(self, ip):
        """Ask user to confirm before rebooting a device."""
        c = self.cards.get(ip)
        if not c: return
        card_name = c["name_label"].value if c.get("name_label") else ip

        def do_cancel(_):
            dlg.open = False
            self.page.update()

        def do_confirm(_):
            dlg.open = False
            self.page.update()
            threading.Thread(target=self.start_reboot, args=(ip,), daemon=True).start()

        dlg = ft.AlertDialog(
            modal=True,
            title=ft.Text("Reboot Device?"),
            content=ft.Column([
                ft.Text(f"Reboot '{card_name}' ({ip})?", size=13),
                ft.Text("Device will go offline for a few seconds then come back.", size=11, color="grey500"),
            ], tight=True, spacing=6),
            actions=[
                ft.ElevatedButton("Reboot", bgcolor="red900", color="white", on_click=do_confirm),
                ft.TextButton("Cancel", on_click=do_cancel),
            ]
        )
        self.page.overlay.append(dlg)
        dlg.open = True
        self.page.update()

    def start_reboot(self, ip):
        """Reboot a WLED device. If live, release from LedFx first then wait 3s.
        After reboot, if device was live, re-activate it in LedFx automatically.
        """
        c = self.cards.get(ip)
        if not c: return
        card_name = c["name_label"].value if c.get("name_label") else ip
        self._open_log()

        # Track whether device was live so we can re-activate after reboot
        _was_live = ip in self.live_ips

        # If device is live, release it first then wait for it to settle
        if _was_live:
            self.log(f"[Reboot] {card_name} — releasing from LedFx first...", color="orange400")
            vid = self.ledfx_ip_to_virtual.get(ip)
            if vid:
                try:
                    requests.put(f"http://localhost:8888/api/virtuals/{vid}",
                                 json={"active": False}, timeout=3)
                except: pass
            self.page.run_task(self._async_set_live, ip, False)
            self.log(f"[Reboot] {card_name} — waiting 3s before reboot...", color="orange400")
            time.sleep(3)

        self.log(f"[Reboot] {card_name} ({ip}) — sending reboot...", color="cyan")
        _reboot_sent = False
        try:
            r = requests.post(f"http://{ip}/json/state", json={"rb": True}, timeout=3)
            self.log(f"[Reboot] {card_name} — POST /json/state rb:true → HTTP {r.status_code}", color="grey500")
            _reboot_sent = r.status_code == 200
            if not _reboot_sent:
                raise Exception(f"HTTP {r.status_code}")
        except requests.exceptions.ConnectionError:
            self.log(f"[Reboot] {card_name} — connection dropped (device rebooting)", color="grey500")
            _reboot_sent = True
        except Exception as ex:
            self.log(f"[Reboot] {card_name} — failed: {ex}", color="red400")

        if not _reboot_sent:
            self.log(f"[Reboot] {card_name} — could not reach device, reboot may not have occurred", color="red400")
            return

        # Wait for device to go offline then come back
        self.log(f"[Reboot] {card_name} — waiting for device to restart...")
        time.sleep(4)
        for attempt in range(15):
            try:
                requests.get(f"http://{ip}/json", timeout=3).json()
                self.log(f"[Reboot] {card_name} — back online.", color="green400")
                self._ping_device(ip, True)
                # Re-activate in LedFx if device was live before reboot
                if _was_live and self.ledfx_running:
                    seg_vids = self.ledfx_segment_vids.get(ip, [])
                    vid = self.ledfx_ip_to_virtual.get(ip)
                    all_vids = ([vid] if vid else []) + seg_vids
                    if all_vids:
                        self.log(f"[Reboot] {card_name} — re-activating in LedFx ({len(all_vids)} virtual(s))...", color="orange400")
                        def _reactivate(vids=all_vids):
                            def _one(v):
                                try:
                                    requests.put(f"http://localhost:8888/api/virtuals/{v}",
                                                 json={"active": True}, timeout=3)
                                except: pass
                            threads = [threading.Thread(target=_one, args=(v,), daemon=True) for v in vids]
                            for t in threads: t.start()
                            for t in threads: t.join(timeout=4)
                        threading.Thread(target=_reactivate, daemon=True).start()
                return
            except: pass
            time.sleep(2)
        self.log(f"[Reboot] {card_name} — did not come back after 30s. Check device manually.", color="red400")

    def confirm_sanitize(self, ip):
        """Show a confirmation dialog warning user to close web UI before sanitizing."""
        def do_cancel(_):
            dlg.open = False
            self.page.update()

        def do_confirm(_):
            dlg.open = False
            self.page.update()
            threading.Thread(target=self.start_sanitize, args=(ip,), daemon=True).start()

        dlg = ft.AlertDialog(
            modal=True,
            title=ft.Text("Sanitize Presets"),
            content=ft.Column([
                ft.Text("Before continuing:", weight="bold", color="yellow700"),
                ft.Text("Close the WLED web UI in your browser for this device.", size=13),
                ft.Text("Sanitize will reboot the device when done. Any unsaved changes in the web UI will be lost and stale presets may cause errors.", size=12, color="grey400"),
                ft.Divider(),
                ft.Text("Click OK once the web UI is closed.", size=13, color="cyan"),
            ], tight=True, width=420, spacing=8),
            actions=[
                ft.ElevatedButton("OK — Web UI is closed", bgcolor="cyan", color="black", on_click=do_confirm),
                ft.TextButton("Cancel", on_click=do_cancel),
            ]
        )
        self.page.overlay.append(dlg)
        dlg.open = True
        self.page.update()

    def start_sanitize(self, ip):
        self._open_log()
        c = self.cards.get(ip)
        if not c:
            return
        card_name = c["name_label"].value if c.get("name_label") else ip
        self.log(f"{card_name} — Sanitize started ({ip})", color="yellow700")

        # Lock button for duration of job
        btn = c["sanitize_btn"]
        btn.disabled = True
        btn.content.value = "SANITIZING..."
        btn.content.color = "orange400"
        try: btn.update()
        except: pass

        try:
            # 1. Fetch and clean presets
            self.log(f"[Sanitize] Fetching presets from {ip}...")
            raw = requests.get(f"http://{ip}/presets.json", timeout=10).json()

            removed = 0
            def strip_bri(obj):
                nonlocal removed
                if isinstance(obj, dict):
                    if "bri" in obj:
                        obj.pop("bri")
                        removed += 1
                    for v in obj.values():
                        strip_bri(v)
                elif isinstance(obj, list):
                    for item in obj:
                        strip_bri(item)

            strip_bri(raw)
            self.log(f"[Sanitize] Removed {removed} brightness value(s). Uploading...")

            # 2. Upload cleaned presets — ensure all keys are strings for valid JSON
            clean_json = json.dumps(raw, ensure_ascii=False)
            upload_files = {"file": ("presets.json", io.BytesIO(clean_json.encode()))}
            requests.post(f"http://{ip}/upload", files=upload_files)
            self.log(f"[Sanitize] Upload complete. Rebooting {ip} to apply...")

            # 3. Reboot device so it reloads presets fresh
            btn.content.value = "REBOOTING..."
            try: btn.update()
            except: pass
            try:
                requests.post(f"http://{ip}/json/state", json={"rb": True}, timeout=5)
            except:
                pass  # device cuts connection immediately on reboot — that's normal

            # 4. Wait for device to go offline then come back
            self.log(f"[Sanitize] Waiting for {ip} to reboot...")
            time.sleep(3)  # give it a moment to actually go down
            for attempt in range(20):
                try:
                    requests.get(f"http://{ip}/json", timeout=3).json()
                    self.log(f"[Sanitize] {ip} is back online. Presets are clean.", color="green400")
                    self.log(f"[Sanitize] NOTE: If the WLED web UI is open, close it and refresh to load the updated presets.")
                    btn.content.value = "SANITIZE"
                    btn.content.color = "yellow700"
                    btn.disabled = False
                    try: btn.update()
                    except: pass
                    return
                except:
                    pass
                time.sleep(3)

            # Timed out waiting
            self.log(f"[Sanitize] {ip} did not come back after reboot — check device manually.", color="red400")

        except Exception as e:
            self.log(f"[Sanitize] Failed for {ip}: {e}", color="red400")

        # Restore button on any failure path
        btn.content.value = "SANITIZE"
        btn.content.color = "yellow700"
        btn.disabled = False
        try: btn.update()
        except: pass

    async def async_add(self, n, i, dt="wled"): self.add_device_card(n, i, True, dt)
    async def _async_update_visuals(self, ip, is_on):
        self._update_card_visuals(ip, is_on)

    def _mh_confirm_ping(self, ip, delay=1.0):
        """Ping MagicHome device after delay to confirm command worked."""
        def _ping():
            time.sleep(delay)
            self._ping_device(ip, True)
        threading.Thread(target=_ping, daemon=True).start()

    def _update_card_visuals(self, ip, is_on):
        """Immediately update card switch, border and glow after a successful command."""
        c = self.cards.get(ip)
        if not c or c.get("_is_custom"): return
        try:
            c["switch"].value = is_on
            if is_on:
                # Rainbow loop will animate from here — set initial on-colour
                c["glow"].bgcolor = "#0a1a1a"
                c["glow"].border = ft.border.all(2, self._hue_to_hex(self.rainbow_hue))
                c["_glow_state"] = "on"
            else:
                # Dim border immediately — rainbow loop will stop animating
                c["glow"].bgcolor = "#16161e"
                c["glow"].border = ft.border.all(2, "#2b2b3b")
                c["_glow_state"] = "off"
            c["card"].update()
            c["glow"].update()
        except: pass

    def _safe_request(self, m, ip, d=None, scene=False):
        """
        Send a WLED state command.

        - Normal mode (scene=False): up to 3 attempts, verify state after each.
          For preset commands (ps), verifies the effect actually changed.
        - Scene mode (scene=True): fire once and return immediately (no retries, no verify).
          Scene reconcile loop is responsible for validation/retry.
        """
        if d is None:
            try:
                return requests.post(f"http://{ip}/json/state", json={}, timeout=2.0).status_code == 200
            except:
                return False

        _card = self.cards.get(ip)
        _disp = (_card["name_label"].value if _card else None) or ip

        # --- Scene mode: fire-and-forget ---
        if scene:
            try:
                resp = requests.post(f"http://{ip}/json/state", json=d, timeout=2.0)
                if resp.status_code != 200:
                    self.log(f"[CMD] {_disp} scene: HTTP {resp.status_code}", color="orange400")
                    return False
                return True
            except Exception as e:
                self.log(f"[CMD] {_disp} scene error: {e}", color="orange400")
                return False

        # --- Normal mode (existing strict behavior) ---
        _pre_fx = None
        if "ps" in d:
            try:
                _pre_state = requests.get(f"http://{ip}/json/state", timeout=1.5).json()
                _pre_fx = _pre_state.get("seg", [{}])[0].get("fx")
            except:
                pass

        for _attempt in range(3):
            try:
                resp = requests.post(f"http://{ip}/json/state", json=d, timeout=2.0)
                if resp.status_code != 200:
                    self.log(f"[CMD] {_disp} attempt {_attempt+1}: HTTP {resp.status_code}", color="orange400")
                    time.sleep(0.2)
                    continue

                time.sleep(0.4)
                state = requests.get(f"http://{ip}/json/state", timeout=1.5).json()

                mismatch = False
                if "on" in d and state.get("on") != d["on"]:
                    mismatch = True
                if "bri" in d and abs(state.get("bri", 0) - d["bri"]) > 3:
                    mismatch = True

                if "ps" in d and _pre_fx is not None:
                    new_fx = state.get("seg", [{}])[0].get("fx")
                    if new_fx == _pre_fx:
                        self.log(f"[CMD] {_disp} attempt {_attempt+1}: preset sent but effect unchanged (fx={new_fx})", color="orange400")
                        mismatch = True

                if not mismatch:
                    if _attempt > 0:
                        self.log(f"[CMD] {_disp} confirmed on attempt {_attempt+1}", color="green400")

                    _is_on = state.get("on")
                    _bri   = state.get("bri")
                    _fx_id = state.get("seg", [{}])[0].get("fx", 0)
                    _fx_name = self.effect_maps.get(ip, {})
                    _fx_str = _fx_name[_fx_id] if isinstance(_fx_name, list) and _fx_id < len(_fx_name) else None

                    self.page.run_task(self.async_update_status, ip, True, None, _is_on, _fx_str, _bri)
                    return True

                if "on" in d or "bri" in d:
                    self.log(f"[CMD] {_disp} attempt {_attempt+1}: mismatch — sent {d}, got on={state.get('on')} bri={state.get('bri')}", color="orange400")

            except Exception as _e:
                self.log(f"[CMD] {_disp} attempt {_attempt+1} error: {_e}", color="orange400")

            if _attempt < 2:
                time.sleep(0.3)

        self.log(f"[CMD] {_disp} failed all 3 attempts", color="red400")
        return False
        
    def _cols_for_width(self, w):
        """Return ideal column count for given window width."""
        if w < 700:  return 1
        if w < 1050: return 2
        if w < 1400: return 3
        if w < 1800: return 4
        return 5

    def _should_use_narrow(self, w):
        """Return True if narrow layout should be used.
        When LedFx is running with scenes visible, the row is very crowded so
        we use a high threshold — effectively always narrow unless maximized.
        When LedFx is not running, use the scene-count based formula.
        """
        scene_count = sum(1 for s in self.scenes if s is not None) + 1
        if self.ledfx_running:
            # Slider + scene toggle + 8 scenes + LedFx buttons fills the row fast.
            # Go narrow unless the window is very wide (near maximized on large screen).
            # Each scene is ~116px, toggle ~130px, LedFx buttons ~290px, power ~430px.
            space_needed = 430 + 290 + 130 + (scene_count * 116) + 200
            return w < space_needed
        else:
            space_needed = 720 + (scene_count * 116) + 200
            return w < space_needed

    def _apply_master_layout(self, w):
        """Switch master bar between wide (1-row) and narrow (2-row) layouts."""
        narrow = self._should_use_narrow(w)
        if self._master_wide.visible == (not narrow):
            return  # no change needed
        self._master_wide.visible   = not narrow
        self._master_narrow.visible = narrow
        try: self.master_bar.update()
        except: pass

    def _apply_col_width(self, w):
        """Update col on every card cell to match current window width."""
        col_map = {1: 60, 2: 30, 3: 20, 4: 15, 5: 12}
        col_val = col_map[self._cols_for_width(w)]
        changed = False
        for ip, c in self.cards.items():
            cell = c.get("cell")
            if cell and cell.col != col_val:
                cell.col = col_val
                changed = True
        if changed:
            try: self.device_list.update()
            except: pass

    def _on_window_resize(self, e):
        """Save window size and maximized state whenever it changes."""
        try:
            win = self.page.window
            w  = win.width
            h  = win.height
            mx = win.maximized
        except AttributeError:
            w  = self.page.window_width
            h  = self.page.window_height
            mx = getattr(self.page, 'window_maximized', False)
        if w and h and w > 100 and h > 100:
            self._win_max = bool(mx)
            if not mx:
                self._win_w = int(w)
                self._win_h = int(h)
            self.save_cache()
            self._apply_col_width(w)
            self._apply_master_layout(w)


    def handle_window_event(self, e):
        if e.data in ["blur", "minimize"]: self.is_focused = False
        elif e.data in ["focus", "restore"]: self.is_focused = True
    def cleanup(self, e):
        self.running = False
        self.brightness_queue.put(None)
        if self._log_fh:
            try: self._log_fh.close()
            except: pass
        self._log_fh = None
        # Give all background threads time to see running=False and stop their UI updates
        # before Flet tears down the websocket — prevents socket.send() exceptions
        time.sleep(0.8)
        try:
            if self.browser:
                self.browser.cancel()
            self.zeroconf.close()
        except: pass

    def _safe_ui_update(self, control):
        """Update a control only if the app is still running."""
        if not self.running: return
        try: control.update()
        except: pass

class WLEDListener:
    def __init__(self, outer): self.outer = outer
    def add_service(self, zc, type_, name):
        info = zc.get_service_info(type_, name)
        if info: self.outer.page.run_task(self.outer.async_add, name, ".".join(map(str, info.addresses[0])))
    def update_service(self, zc, type_, name): self.add_service(zc, type_, name)
    def remove_service(self, zc, type_, name): pass

def main(page: ft.Page): WLEDApp(page)
if __name__ == "__main__":
    ft.app(target=main)