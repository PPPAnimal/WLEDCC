""" WLEDCC - WLED COMMAND CENTER
    Copyright (C) 2026 Bill Sullivan (SullySSignS)

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <https://www.gnu.org/licenses/>. """

# If you find this software useful, consider supporting the developer.
# [Buy Me a Coffee] https://paypal.me/BillSullivan02
# Inquiries: privatebillsullivan@gmail.com
# 
# 
# 
# ledfx_monitor_loop
# fetch_latest_release
# check_ledfx_updates
# brightness_worker
# rainbow_loop
# unified_poll_loop
#
#
#
#
#

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
import shutil
from queue import Queue
import psutil
import platform
from datetime import datetime
import glob
import random
import math
import win32gui
import win32con
import ctypes
try:
    import winreg
except Exception:
    winreg = None

def raise_if_running(window_title):
    """If window exists, bring to front and return True, else False."""
    hwnd = win32gui.FindWindow(None, window_title)
    if hwnd:
        # If minimized, restore
        if win32gui.IsIconic(hwnd):
            win32gui.ShowWindow(hwnd, win32con.SW_RESTORE)
        # Bring to foreground
        win32gui.SetForegroundWindow(hwnd)
        return True
    return False

import sys as _sys
_VERSION_DIR = os.path.dirname(_sys.executable if getattr(_sys, 'frozen', False) else os.path.abspath(__file__))
_VERSION_FILE = os.path.join(_VERSION_DIR, "version.txt")
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
WLEDCC_RELEASES_API_URL = "https://api.github.com/repos/PPPAnimal/WLEDCC/releases/latest"
WLEDCC_RELEASES_LIST_URL = "https://api.github.com/repos/PPPAnimal/WLEDCC/releases?per_page=20"
WLEDCC_RELEASES_PAGE_URL = "https://github.com/PPPAnimal/WLEDCC/releases/latest"
WINAMP_DOWNLOADS_PAGE_URL = "https://winamp.com/player"
WINAMP_LEGACY_INSTALLER_URL = "https://download.winamp.com/winamp/winamp_latest_full.exe"
DEFAULT_WINAMP_CARD_KEY = "__default_winamp__"
SPOTIFY_DOWNLOADS_PAGE_URL = "https://www.spotify.com/download/windows/"
SPOTIFY_SETUP_EXE_URL = "https://download.scdn.co/SpotifySetup.exe"
DEFAULT_SPOTIFY_CARD_KEY = "__default_spotify__"
MAGIC_HOME_PORT = 5577
MAGIC_HOME_DISCOVERY_PORT = 48899

# Unified polling configuration for optimal ESP32 performance
WLED_BASE_INTERVAL = 5.0    # Base seconds between WLED poll rounds
WLED_SCALE_FACTOR = 2.0     # Additional seconds per 10 devices
WLED_MAX_INTERVAL = 15.0    # Maximum polling interval (cap)
LEDFX_POLL_INTERVAL = 3.0    # Fixed LedFx API poll interval
UNFOCUSED_PAUSE = 5.0       # Polling pause when app window not focused

# MagicHome built-in modes (single source of truth for UI + ping decode)
MH_MODES = [
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
MH_MODE_NAME_BY_PATTERN = {pat: label for (label, _desc, pat) in MH_MODES if pat is not None}

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
        self.unfocused_updates_enabled = True  # polls continue while app is out of focus
        self.running = True  
        # --- Slider drag smoothing ---
        self._dragging = set()
        self._pending_bri = {}
        self._last_slider_ui = {}
        self._last_defer_log = {}
        self.is_refreshing = False
        self.latest_release_ver = None
        self.wledcc_latest_ver = None
        self.wledcc_download_url = None
        self.wledcc_asset_name = None
        self.ledfx_latest_ver = None
        self.ledfx_current_ver = "2.0.0" 
        self.brightness_queue = Queue()
        self.rainbow_hue = 0  # shared hue position for all ON-card animations
        # Title animation settings
        self.title_effect = "rainbow_wave"  # rainbow_wave, color_loop, breathing, strobe, solid
        self.title_speed  = 11.0            # hue step per tick (default 50% of 2-20 range)
        self.title_color  = "#ff0000"       # base color for non-rainbow effects
        # Border animation settings
        self.border_effect = "color_loop"   # rainbow_wave, color_loop, breathing, strobe, solid
        self.border_speed  = 11.0
        self.border_color  = "#ff0000"
        # Internal animation state
        self._breath_title = 0.0
        self._breath_title_dir = 1
        self._breath_border = 0.0
        self._breath_border_dir = 1
        self._strobe_title = True
        self._strobe_border = True
        # Winamp-style spectrum analyzer state (header visualizer)
        self._spec_bands = 30
        self._spec_analysis_bands = 30
        self._spec_levels = 16
        self._spec_bars = [0.0] * self._spec_analysis_bands
        self._spec_peaks = [0.0] * self._spec_analysis_bands
        self._spec_peak_hold = [0] * self._spec_analysis_bands
        self._spec_band_avg = [0.0] * self._spec_analysis_bands  # per-band adaptive floor for dynamics
        self._spec_segments = []
        self._spec_gain = 1.0
        self._spec_target_fps = 25
        self._spec_sensitivity = 0.85  # 0.1-1.5 user preamp scale, default 85%
        self._spec_reactivity = 3.0  # rise speed multiplier
        self._spec_bar_decay = 2.0   # bar fall speed multiplier
        self._spec_peak_decay = 1.0  # peak fall speed multiplier
        self._spec_mode = "classic"  # classic | vu | random | random_song
        self._spec_mode_random_current = "classic"
        self._spec_mode_random_cycle_seconds = 60.0
        self._spec_mode_random_next_ts = time.monotonic() + self._spec_mode_random_cycle_seconds
        self._spec_mode_song_silence_seconds = 1.0
        self._spec_mode_song_switch_armed = True
        self._spec_capture_channels = 2  # prefer stereo; fallback to mono if device does not support it
        self._spec_sample_rate = 48000  # lower values reduce analyzer CPU usage
        self._spec_sampling_enabled = True  # quick toggle: when off, skip audio capture (idle-only mode)
        self._spec_vu_gain = 0.18
        self._spec_vu_left = 0.0
        self._spec_vu_right = 0.0
        self._spec_vu_peak_left = 0.0
        self._spec_vu_peak_right = 0.0
        self._spec_idle_enabled = True
        self._spec_idle_timeout = 2.0
        self._spec_idle_effect = "random"  # random | aurora | pulse | text | rainbow | pacman | tetris | invaders | snake | starwars
        self._spec_idle_cycle_effects = ["aurora", "pulse", "text", "rainbow", "pacman", "tetris", "invaders", "snake", "starwars"]
        self._spec_idle_speed = 2.0  # ambient idle animation speed multiplier
        self._spec_idle_random_current = "aurora"
        self._spec_idle_random_cycle_seconds = 10.0
        self._spec_idle_random_next_ts = time.monotonic() + self._spec_idle_random_cycle_seconds
        self._spec_idle_threshold = 0.02
        self._spec_idle_active = False
        self._spec_last_audio_ts = time.monotonic()
        self._spec_idle_text = " SPECTRUM ANALYZER "
        self._spec_idle_scroll = 0
        self._spec_idle_phase = 0.0
        self._spec_eq_freqs = [60, 170, 310, 600, 1000, 3000, 6000, 12000, 14000, 15000]
        self._spec_eq_gains = [1.0] * len(self._spec_eq_freqs)  # UI-only visual EQ multipliers
        self._spec_log_once = False
        self._spec_no_audio_warned = False
        self._spec_audio_sources = []  # list of (name, id) tuples for available audio devices
        self._spec_source_order = []  # preferred source ordering by name (selected source pinned first)
        self._spec_selected_source = None  # selected audio source name or None for default
        self._spec_profiles = {}  # per-source analyzer profiles: sensitivity + eq gains
        self._spec_preview_pending = False  # unsaved preview session active across dialog reopen
        self._spec_preview_snapshot = None  # baseline state to restore on Close/Refresh
        self._spec_source_changed = False  # flag to signal audio loop to switch source
        self._spec_disabled = False  # True if audio capture failed and is disabled
        self._spec_render_mode = "grid"  # grid | graphics
        self._spec_box_grid_size = (296, 62)
        self._spec_box_graphics_size = self._spec_box_grid_size
        self._spec_grid_content = None
        self._spec_graphics_host = None
        self._spec_graphics_layer = None
        self._spec_graphics_ready = False
        self._spec_graphics_stars = []
        self._spec_graphics_lines = []
        self._spec_graphics_view_size = (0, 0)
        self._spec_display_cleared = False
        self._spec_np_patch_applied = False
        self.brightness_debounce_timer = None
        self._save_timer = None          # debounce timer for save_cache
        self._session_backup_written = False  # write one backup per session only
        self.current_master_bri = 128
        self.prev_master_bri = 128
        self.individual_brightness = {}
        self.custom_names = {}  # ip -> user-defined display name
        self.display_names = {}  # ip -> last known display name shown on card
        self.preset_cache = {}   # ip -> {id: name} dict of presets
        self.playlist_preset_first = {}  # ip -> {preset_id: first child preset id} for playlist verification
        self.active_preset = {}  # ip -> currently active preset ID (-1 = none/effect only)
        self.last_selected_preset = {}  # ip -> last user/confirmed preset ID (sticky for playlist scene saves)
        self.scenes = [None, None, None, None]  # 4 scene slots, each None or {name, data}
        self.card_order = []  # ordered list of IPs matching last saved visual order
        self.device_macs = {}    # ip -> mac_suffix (last 6 chars of MAC)
        self.custom_devices = {}  # key -> {name, url, is_local} for non-WLED/MH devices
        self.custom_launch_state = {}  # key -> {kind, pid, managed, path/url, browser}
        self._spotify_play_state = {}  # key -> bool (best-effort playback state for spotify.com cards)
        self._spotify_keepalive_until = {}  # key -> monotonic ts to avoid UI state flapping on tab/title changes
        self._default_custom_cards_meta = {
            DEFAULT_WINAMP_CARD_KEY: {"auto_created": False, "user_deleted": False},
            DEFAULT_SPOTIFY_CARD_KEY: {"auto_created": False, "user_deleted": False},
        }
        self._spotify_media_listener_thread = None
        self._spotify_media_listener_stop = threading.Event()
        self._spotify_media_listener_active = False
        self._spotify_media_listener_backend = None
        self._spotify_media_last_state = None
        self._spotify_media_last_track = None
        self._spotify_listener_loaded_at_start = None
        self._spotify_media_listener_earliest_ts = time.monotonic() + 3.0
        self._spotify_listener_grace_until = 0.0
        self._spotify_silence_grace_sec = 25.0
        self._spotify_window_seen_until = 0.0
        self._spotify_window_tip_shown = False
        self._spotify_title_log_cache = {}
        self._chrome_tab_cache = None
        self._chrome_tab_cache_ts = 0.0
        self.mac_to_ip = {}      # mac_suffix -> current ip
        self.card_ids = {}        # ip -> stable UUID for this card
        self.card_id_to_ip = {}   # UUID -> current ip (updated on IP change)
        self.merge_mode = False   # True while user is in merge mode
        self.debug_mode = False   # True = show verbose debug logs
        self.debug_on_open = False   # True = enable debug mode when log panel opens
        self.log_auto_open = False   # True = log panel opens automatically at startup
        # Exit popup preferences
        self.exit_auto_stop_ledfx = False
        self.exit_auto_all_off = False
        self._cleanup_started = False
        self._exit_in_progress = False
        self.exit_dialog = None
        self.exit_status_text = None
        self.exit_stop_ledfx_auto_cb = None
        self.exit_all_off_auto_cb = None
        self.exit_ledfx_service_auto_cb = None
        self.exit_wled_scene_auto_cb = None
        self.exit_ledfx_scene_auto_cb = None
        # --- Log de-dup + change tracking ---
        self._last_log_by_key = {}
        self._last_ping_state = {}
        self._last_ledfx_state = {}
        self.draggable_map = {}   # flet control uid -> ip, for drag resolution
        self.scene_btn_refs = {}  # idx -> Container ref for rainbow border on active scene
        self.active_scene_idx = None  # which scene is currently active (glowing)
        self.ledfx_running = False  # mirrors ledfx_monitor_loop — used to skip polls
        self._ledfx_launching = False  # True while launch sequence is running
        self.auto_start_ledfx_on_launch = False
        self.auto_restore_wled_scene = False
        self.auto_restore_ledfx_scene = False
        self.last_ledfx_scene_id = None
        self.active_ledfx_scene_id = None
        self.last_wled_scene_idx = None
        self._pending_ledfx_scene_restore = False
        self._restore_wled_scene_on_ledfx_stop = False
        self._ledfx_autostart_attempted = False
        self.ledfx_scene_btn_refs = {}  # scene_id -> [Container, ...] for active LedFx scene glow
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
        self.ledfx_scene_virtuals = {}  # scene_id -> {virtual_id: bool(active_in_scene)}
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

        self.save_logs_to_disk = False  # True = write UI log lines to session file

        # Session log file is opened only when save_logs_to_disk is enabled
        self._log_fh = None
        self._session_log_path = None
        self.file_picker = ft.FilePicker(on_result=self.on_file_result)
        self.page.overlay.append(self.file_picker)
        self._exe_pick_callback = None          # set before opening exe_picker
        self.exe_picker = ft.FilePicker(on_result=self._on_exe_pick_result)
        self.page.overlay.append(self.exe_picker)

        self.load_cache()
        _default_cards_seeded = self._seed_default_custom_cards()
        if self.save_logs_to_disk:
            self._log_fh = self._open_session_log()
        self.setup_ui()
        if _default_cards_seeded:
            self.save_cache()
        
        # Apply startup preferences: if auto-open is on, log_container was set visible
        # in setup_ui already. If debug_on_open is also on, activate debug mode now.
        if self.log_auto_open and self.debug_on_open:
            self.debug_mode = True
            self._sync_debug_button_state()

        self.log(f"System initialized. Version {APP_VERSION}", color="white")
        self.log(f"[Version] Reading from: {_VERSION_FILE}", color="grey500")
        if getattr(self, "_cache_load_warning", None):
            self.log(self._cache_load_warning, color="red400")
        threading.Thread(target=self.fetch_latest_release, daemon=True).start()
        threading.Thread(target=self.check_wledcc_updates, daemon=True).start()
        threading.Thread(target=self.check_ledfx_updates, daemon=True).start()
        threading.Thread(target=self.brightness_worker, daemon=True).start()
        threading.Thread(target=self.rainbow_loop, daemon=True).start()
        threading.Thread(target=self.ledfx_monitor_loop, daemon=True).start()
        threading.Thread(target=self.unified_poll_loop, daemon=True).start()
        threading.Thread(target=self._startup_ledfx_autostart, daemon=True).start()
        threading.Thread(target=self._run_custom_autolaunches, daemon=True).start()
        threading.Thread(target=self._custom_launcher_monitor_loop, daemon=True).start()
        threading.Thread(target=self._audio_analyzer_loop, daemon=True).start()
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
        """Open the current session log file (single file reused for this app session)."""
        try:
            if not self._session_log_path:
                # Rotate only when creating a brand-new session file
                pattern = os.path.join(LOG_DIR, "wled_session_*.log")
                existing = sorted(glob.glob(pattern))
                while len(existing) >= LOG_MAX:
                    os.remove(existing.pop(0))
                ts = datetime.now().strftime("%Y%m%d_%H%M%S")
                self._session_log_path = os.path.join(LOG_DIR, f"wled_session_{ts}.log")

            is_new_file = not os.path.exists(self._session_log_path)
            fh = open(self._session_log_path, "a", encoding="utf-8", buffering=1)
            if is_new_file:
                ts = datetime.now().strftime("%Y%m%d_%H%M%S")
                fh.write(f"=== WLED App Session {ts} ===\n")
            return fh
        except Exception:
            return None

    def log(self, message, color="grey300"):
        timestamp = datetime.now().strftime("%H:%M:%S")
        self.log_lines.controls.append(
            ft.Text(f"[{timestamp}] {message}", size=11, color=color, selectable=True)
        )
        # Trim oldest entries to keep UI responsive — file log keeps full history
        if len(self.log_lines.controls) > 500:
            del self.log_lines.controls[:100]  # drop oldest 100 at a time
        # Write to session log file only when enabled
        if self.save_logs_to_disk and self._log_fh:
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
        if self.debug_mode:
            self._last_log_by_key.clear()
            self._last_ping_state.clear()
            self._last_ledfx_state.clear()
        self._sync_debug_button_state()
        self.log(f"[Debug] Debug mode {'ON' if self.debug_mode else 'OFF'}", 
                 color="orange400" if self.debug_mode else "grey400")

    def _sync_debug_button_state(self):
        self._debug_btn_text.value = "DEBUG: ON" if self.debug_mode else "DEBUG: OFF"
        self._debug_btn_text.color = "orange400" if self.debug_mode else "grey400"
        try: self.debug_btn.update()
        except: pass

    def _on_debug_on_open_change(self, e):
        self.debug_on_open = e.control.value
        self.save_cache()
        self.log(f"[Debug] 'Debug on open' {'enabled' if self.debug_on_open else 'disabled'}", color="grey500")

    def _on_log_auto_open_change(self, e):
        self.log_auto_open = e.control.value
        self.save_cache()
        self.log(f"[Log] 'Auto-open log' at startup {'enabled' if self.log_auto_open else 'disabled'}", color="grey500")

    def _on_unfocused_updates_change(self, e):
        self.unfocused_updates_enabled = bool(e.control.value)
        self.save_cache()
        if self.unfocused_updates_enabled:
            self.log("[Focus] Background Log and UI updates enabled while unfocused.", color="grey500")
        else:
            self.log("[Focus] Background Log and UI updates disabled while unfocused.", color="grey500")

    def _on_save_logs_to_disk_change(self, e):
        self.save_logs_to_disk = bool(e.control.value)
        if self.save_logs_to_disk:
            if self._log_fh is None:
                self._log_fh = self._open_session_log()
            self.log("[Log] 'Save logs to disk' enabled", color="grey500")
        else:
            self.log("[Log] 'Save logs to disk' disabled", color="grey500")
            if self._log_fh:
                try: self._log_fh.close()
                except: pass
                self._log_fh = None
        self.save_cache()

    def dbg(self, message, color="grey500"):
        """Log only when debug mode is on."""
        if self.debug_mode:
            self.log(f"[DBG4 TRACE] {message}", color=color)

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

        return self.log_unique(key, f"[DBG3 STATE] {message}", color=color)


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

        self.log_unique(f"ping:{ip}", f"[DBG1] WLED PING {msg}", color="white")


    def _dbg_ledfx_poll(self, ip, vid, active, streaming, bri, effect_name):

        if not self.debug_mode:

            return

        state = {"active": bool(active), "streaming": bool(streaming), "bri": str(bri), "effect": str(effect_name)}
        state_key = f"{ip}:{vid}"

        last = self._last_ledfx_state.get(state_key)

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

        self._last_ledfx_state[state_key] = state

        msg = f"LedFx Poll {vid} ({ip}): "

        msg += "active=" + self._mark("active", changed, str(state["active"])) + " "

        msg += "streaming=" + self._mark("streaming", changed, str(state["streaming"])) + " "

        msg += "bri=" + self._mark("bri", changed, state["bri"]) + " "

        msg += "effect=" + self._mark("effect", changed, state["effect"])

        msg += "  Δ " + ",".join(changed)

        self.log_unique(f"ledfx:{ip}:{vid}", f"[DBG2] LEDFX POLL {msg}", color="white")


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
            self._sync_debug_button_state()
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
                self._sync_debug_button_state()
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
                if self.auto_restore_ledfx_scene and self.last_ledfx_scene_id:
                    self._pending_ledfx_scene_restore = True
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
                    time.sleep(5)
                    if not self.running or not self.ledfx_running:
                        return
                    if self._scene_mode != "ledfx":
                        self.toggle_scene_mode()
                    else:
                        threading.Thread(target=self._fetch_ledfx_scenes, daemon=True).start()
                    
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
                if self._restore_wled_scene_on_ledfx_stop and self.auto_restore_wled_scene:
                    self._restore_wled_scene_on_ledfx_stop = False
                    threading.Thread(
                        target=lambda: self._restore_last_wled_scene_after_delay(delay=2.5, source="ledfx-stop"),
                        daemon=True,
                    ).start()
                else:
                    self._restore_wled_scene_on_ledfx_stop = False
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

    def _on_ledfx_auto_start_change(self, e):
        v = bool(e.control.value)
        # Legacy hook retained for compatibility with older UI controls.
        self.auto_start_ledfx_on_launch = v
        self._pending_ledfx_scene_restore = bool(self.last_ledfx_scene_id and self.auto_restore_ledfx_scene)
        self.save_cache()

    def _startup_ledfx_autostart(self):
        # Brief settle delay, then restore WLED scene (if enabled).
        time.sleep(6)
        if (
            self.running
            and self.auto_restore_wled_scene
            and (not self.auto_start_ledfx_on_launch)
            and self.last_wled_scene_idx is not None
        ):
            idx = self.last_wled_scene_idx
            if idx < len(self.scenes) and self.scenes[idx] is not None:
                self.log(f"[Scene Auto] Restoring last WLED scene: '{self.scenes[idx]['name']}'", color="cyan")
                scene_result = self.activate_scene(idx, source="auto", wait=True, timeout=45)
                if scene_result is None:
                    self.log("[Scene Auto] WLED restore still settling after 45s; continuing startup", color="orange400")
                elif scene_result.get("failed"):
                    self.log(
                        f"[Scene Auto] WLED restore finished with {len(scene_result['failed'])} unconfirmed device(s); continuing startup",
                        color="orange400",
                    )
                else:
                    self.log("[Scene Auto] WLED restore confirmed before LedFx startup", color="green400")
        elif self.running and self.auto_restore_wled_scene and self.auto_start_ledfx_on_launch:
            self.log("[Scene Auto] Skipping startup WLED restore because LedFx auto-start is enabled", color="grey500")

        if not self.running:
            return

        if self.auto_start_ledfx_on_launch:
            if self.is_ledfx_running():
                self.log("[LedFx Auto] LedFx already running at startup", color="grey500")
            else:
                self._ledfx_autostart_attempted = True
                self.log("[LedFx Auto] Auto-start enabled — launching LedFx", color="purple")
                if not self.ledfx_path or not os.path.exists(self.ledfx_path):
                    auto_path = self._find_ledfx_locally()
                    if auto_path:
                        self.ledfx_path = auto_path
                        self.save_cache()
                        self.log(f"[LedFx Auto] Found LedFx at: {auto_path}", color="green400")
                    else:
                        self.log("[LedFx Auto] LedFx path not found. Use START LEDFX once to configure.", color="orange400")
                if self.ledfx_path and os.path.exists(self.ledfx_path):
                    self._launch_ledfx()

        if self.auto_restore_ledfx_scene and self.last_ledfx_scene_id:
            self._pending_ledfx_scene_restore = True
            self.log("[LedFx Auto] Last LedFx scene queued; will restore after LedFx scenes load", color="grey500")

    def _restore_last_wled_scene_after_delay(self, delay=2.5, source="toggle"):
        """Restore saved WLED scene after UI settles."""
        time.sleep(delay)
        if source == "ledfx-stop":
            deadline = time.time() + 25
            while self.running and self.live_ips and time.time() < deadline:
                time.sleep(0.5)
            if self.live_ips:
                self.log(
                    f"[Scene Auto] LedFx stop restore timed out waiting for release on {len(self.live_ips)} device(s); continuing",
                    color="orange400",
                )
            else:
                self.log("[Scene Auto] WLED release confirmed after LedFx stop", color="green400")
        if not self.running or not self.auto_restore_wled_scene:
            return
        idx = self.last_wled_scene_idx
        if idx is None or idx >= len(self.scenes) or self.scenes[idx] is None:
            return
        scene_name = self.scenes[idx].get("name", f"Scene {idx + 1}")
        self.log(f"[Scene Auto] Restoring last WLED scene ({source}): '{scene_name}'", color="cyan")
        threading.Thread(target=lambda: self.activate_scene(idx, source="auto"), daemon=True).start()

    def _schedule_ledfx_scene_restore_after_delay(self, delay=2.5):
        """Restore saved LedFx scene after LedFx buttons/scenes are loaded."""
        if not self.auto_restore_ledfx_scene or not self.last_ledfx_scene_id:
            return
        self._pending_ledfx_scene_restore = True

        def _runner():
            time.sleep(delay)
            if not self.running or not self.ledfx_running or self._scene_mode != "ledfx":
                return
            self._try_restore_last_ledfx_scene()

        threading.Thread(target=_runner, daemon=True).start()

    def _wait_for_ledfx_then_restore_scene(self):
        """Wait for LedFx availability and UI scene toggle, then restore last used scene."""
        announced_wait = False
        announced_toggle = False
        while self.running and self._pending_ledfx_scene_restore:
            if not self.is_ledfx_running():
                # LedFx not running yet — keep waiting
                if not announced_wait:
                    self.log("[LedFx Auto] Waiting for LedFx launch to restore last scene", color="grey500")
                    announced_wait = True
                time.sleep(2)
                continue
            
            # LedFx is running — now wait for UI scene mode toggle to complete
            if self._scene_mode != "ledfx":
                if not announced_toggle:
                    self.log("[LedFx Auto] Waiting for scene toggle to complete...", color="grey500")
                    announced_toggle = True
                time.sleep(1)
                continue
            
            # Scene mode toggle is complete — toggle's automatic fetch will populate scenes
            # and call _try_restore_last_ledfx_scene automatically. Just return here.
            self.log("[LedFx Auto] Scene mode switched to LedFx, restore pending...", color="grey500")
            return

    def _activate_ledfx_scene(self, scene_id, scene_name=None, remember=True, source="manual"):
        label = scene_name or self.ledfx_scenes.get(scene_id) or scene_id
        # Wake only virtuals marked active inside the selected scene.
        scene_virtuals = self.ledfx_scene_virtuals.get(scene_id, {})
        wake_vids = [vid for vid, is_active in scene_virtuals.items() if is_active]
        if wake_vids:
            self.dbg(f"[LedFx Scene] Pre-wake {len(wake_vids)} active scene virtual(s) for '{label}'")
            for vid in wake_vids:
                try:
                    requests.put(
                        "http://localhost:8888/api/virtuals",
                        json={"id": vid, "active": True},
                        timeout=1.2,
                    )
                except Exception:
                    pass
        try:
            r = requests.put(
                "http://localhost:8888/api/scenes",
                json={"action": "activate", "id": scene_id},
                timeout=3,
            )
            if r.status_code in (200, 204):
                self.active_ledfx_scene_id = scene_id
                if remember and self.last_ledfx_scene_id != scene_id:
                    self.last_ledfx_scene_id = scene_id
                    self.save_cache()
                self._apply_ledfx_scene_glow()
                if source == "auto":
                    self.log(f"[LedFx Auto] Restored last scene: '{label}'", color="purple")
                else:
                    self.log(f"[LedFx Scene] '{label}' activated", color="purple")
                return True
            self.log(f"[LedFx Scene] '{label}' failed: HTTP {r.status_code}", color="red400")
            return False
        except Exception as ex:
            self.log(f"[LedFx Scene] '{label}' error: {ex}", color="red400")
            return False

    def _try_restore_last_ledfx_scene(self):
        if not self.running or not self.ledfx_running or not self._pending_ledfx_scene_restore:
            return
        sid = self.last_ledfx_scene_id
        if not sid:
            self._pending_ledfx_scene_restore = False
            return
        if sid not in self.ledfx_scenes:
            # Keep pending true so a later scene fetch can still restore (e.g. LedFx
            # still warming up and returning empty scenes initially).
            self.log("[LedFx Auto] Saved scene not in current LedFx list yet — waiting...", color="orange400")
            return
        self._pending_ledfx_scene_restore = False
        threading.Thread(
            target=lambda: self._activate_ledfx_scene(sid, self.ledfx_scenes.get(sid), remember=False, source="auto"),
            daemon=True,
        ).start()

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
            # Try to get friendly name from cards if available
            card = None
            for _ip, _c in self.cards.items():
                if _ip == ip:
                    card = _c
                    break
            card_name = (card.get("name_label").value if card and card.get("name_label") else None) or ip
            self.dbg_unique(f"ledfx_mdns:{hostname}",
                            f"[LedFx Poll] {card_name}, {ip} — mDNS resolved from '{hostname}'",
                            color="grey500")
            return ip
        except Exception as e:
            count = self._ledfx_resolve_fails.get(hostname, 0) + 1
            self._ledfx_resolve_fails[hostname] = count
            if count <= 3:
                self.log(f"[LedFx Poll] ?, ? — mDNS resolution failed for '{hostname}': {e}", color="orange400")
            # silently skip after 3 failures — will retry if LedFx clears cache on stop
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
            self._restore_wled_scene_on_ledfx_stop = True
            self._stop_ledfx_process(log_prefix="[LedFx]")
        else:
            if not self.ledfx_path or not os.path.exists(self.ledfx_path):
                # Path is missing or broken — try to find it automatically
                self.log("LedFx path unknown. Searching local drives...", color="blue400")
                auto_path = self._find_ledfx_locally()
                
                if auto_path:
                    self.ledfx_path = auto_path
                    self.save_cache() # Save it to your JSON immediately
                    self.log(f"✓ LedFx auto-located at: {auto_path}", color="green400")
                    self._launch_ledfx()
                else:
                    # Still nothing? Show the setup dialog
                    self._show_ledfx_setup_dialog()
            else:
                # Path exists in JSON and is valid — just launch
                self._launch_ledfx()

    def _stop_ledfx_process(self, log_prefix="[LedFx]"):
        """Stop LedFx only; never starts it."""
        stopped = False
        for proc in psutil.process_iter(['name']):
            try:
                if proc.info['name'] and proc.info['name'].lower() == "ledfx.exe":
                    proc.kill()
                    stopped = True
            except:
                pass
        if stopped:
            self.log(f"{log_prefix} Process terminated.", color="orange400")
        else:
            self.log(f"{log_prefix} Process not running.", color="grey500")
        return stopped

    def _on_exit_pref_change(self, e=None):
        if self.exit_stop_ledfx_auto_cb is not None:
            self.exit_auto_stop_ledfx = bool(self.exit_stop_ledfx_auto_cb.value)
        if self.exit_all_off_auto_cb is not None:
            self.exit_auto_all_off = bool(self.exit_all_off_auto_cb.value)
        if self.exit_ledfx_service_auto_cb is not None:
            self.auto_start_ledfx_on_launch = bool(self.exit_ledfx_service_auto_cb.value)
        if self.exit_wled_scene_auto_cb is not None:
            self.auto_restore_wled_scene = bool(self.exit_wled_scene_auto_cb.value)
        if self.exit_ledfx_scene_auto_cb is not None:
            self.auto_restore_ledfx_scene = bool(self.exit_ledfx_scene_auto_cb.value)

        if self.exit_wled_scene_auto_cb is not None:
            self.exit_wled_scene_auto_cb.value = self.auto_restore_wled_scene
        if self.exit_ledfx_scene_auto_cb is not None:
            self.exit_ledfx_scene_auto_cb.value = self.auto_restore_ledfx_scene

        if not self.auto_restore_ledfx_scene:
            self._pending_ledfx_scene_restore = False
        elif self.last_ledfx_scene_id:
            self._pending_ledfx_scene_restore = True
        self.save_cache()

    def _persist_exit_preferences(self, flush=False):
        self._on_exit_pref_change()
        if flush:
            if self._save_timer is not None:
                self._save_timer.cancel()
                self._save_timer = None
            self._do_save_cache()

    def _run_exit_stop_ledfx(self, auto=False):
        prefix = "[Exit Auto]" if auto else "[Exit]"
        self._stop_ledfx_process(log_prefix=prefix)
        if self.exit_status_text is not None:
            self.exit_status_text.value = "LedFx stop command sent."
            try: self.exit_status_text.update()
            except: pass

    def _run_exit_all_off(self, auto=False):
        prefix = "[Exit Auto]" if auto else "[Exit]"
        self.log(f"{prefix} Running ALL OFF for all devices...", color="cyan")
        # On confirmed app close, kick ALL OFF immediately but cap wait time.
        # This prevents intermittent UI lockups if reconcile loops take too long.
        if auto:
            done = threading.Event()

            def _run_and_signal():
                try:
                    self.broadcast_power(False, wait=True)
                finally:
                    done.set()

            threading.Thread(target=_run_and_signal, daemon=True).start()
            if not done.wait(timeout=8.0):
                self.log(f"{prefix} ALL OFF still reconciling; continuing app exit.", color="orange400")
        else:
            self.broadcast_power(False, wait=False)
        if self.exit_status_text is not None:
            self.exit_status_text.value = "All Off command sent."
            try: self.exit_status_text.update()
            except: pass

    def _close_exit_dialog(self, e=None):
        if self.exit_dialog is not None:
            self.exit_dialog.open = False
            try: self.page.update()
            except: pass

    def _show_exit_dialog(self):
        if self._exit_in_progress:
            return

        if self.exit_dialog is None:
            self.exit_status_text = ft.Text("", size=11, color="grey400")
            self.exit_stop_ledfx_auto_cb = ft.Checkbox(
                label="Auto-run on exit",
                value=self.exit_auto_stop_ledfx,
                on_change=self._on_exit_pref_change,
                scale=0.9,
            )
            self.exit_all_off_auto_cb = ft.Checkbox(
                label="Auto-run on exit",
                value=self.exit_auto_all_off,
                on_change=self._on_exit_pref_change,
                scale=0.9,
            )
            self.exit_ledfx_service_auto_cb = ft.Checkbox(
                label="Auto-start LedFx on app launch",
                value=self.auto_start_ledfx_on_launch,
                on_change=self._on_exit_pref_change,
                scale=0.9,
            )
            self.exit_wled_scene_auto_cb = ft.Checkbox(
                label="Auto-load last WLED scene",
                value=self.auto_restore_wled_scene,
                on_change=self._on_exit_pref_change,
                scale=0.9,
            )
            self.exit_ledfx_scene_auto_cb = ft.Checkbox(
                label="Auto-load last LedFx scene",
                value=self.auto_restore_ledfx_scene,
                on_change=self._on_exit_pref_change,
                scale=0.9,
            )

            self.exit_dialog = ft.AlertDialog(
                modal=True,
                title=ft.Text("Before Closing App", color="orange400"),
                content=ft.Column([
                    ft.Text("Choose actions before exit:", size=12, color="grey300"),
                    ft.Row([
                        ft.ElevatedButton("Stop LedFx", on_click=lambda _: self._run_exit_stop_ledfx(auto=False), bgcolor="red900", color="white"),
                        self.exit_stop_ledfx_auto_cb,
                    ], spacing=10, vertical_alignment=ft.CrossAxisAlignment.CENTER),
                    ft.Row([
                        ft.ElevatedButton("All Off", on_click=lambda _: self._run_exit_all_off(auto=False), bgcolor="red900", color="white"),
                        self.exit_all_off_auto_cb,
                    ], spacing=10, vertical_alignment=ft.CrossAxisAlignment.CENTER),
                    ft.Row([
                        self.exit_ledfx_service_auto_cb,
                    ], spacing=10, vertical_alignment=ft.CrossAxisAlignment.CENTER),
                    ft.Row([
                        self.exit_wled_scene_auto_cb,
                    ], spacing=10, vertical_alignment=ft.CrossAxisAlignment.CENTER),
                    ft.Row([
                        self.exit_ledfx_scene_auto_cb,
                    ], spacing=10, vertical_alignment=ft.CrossAxisAlignment.CENTER),
                    self.exit_status_text,
                    ft.Divider(height=5, color="grey700"),
                    ft.Text("Enjoying WLEDCC?  Consider buying me a coffee.", size=11, color="grey400"),
                    ft.Row([
                        ft.GestureDetector(
                            content=ft.Image(
                                src="https://www.paypalobjects.com/en_US/i/btn/btn_donate_LG.gif",
                                height=18,
                                fit=ft.ImageFit.CONTAIN,
                                tooltip="Donate via hosted PayPal button",
                            ),
                            on_tap=lambda _: self.page.launch_url("https://www.paypal.com/donate/?hosted_button_id=DLFMQSFHUZ28S"),
                            mouse_cursor=ft.MouseCursor.CLICK,
                        ),
                    ], spacing=12, vertical_alignment=ft.CrossAxisAlignment.CENTER),
                ], tight=True, spacing=10, width=450),
                actions=[
                    ft.TextButton("Cancel", on_click=self._close_exit_dialog),
                    ft.ElevatedButton("Close App", bgcolor="orange400", color="black", on_click=self._confirm_app_close),
                ],
                actions_alignment=ft.MainAxisAlignment.END,
            )
            self.page.overlay.append(self.exit_dialog)

        # Load current preferences into dialog controls each time it opens.
        self.exit_stop_ledfx_auto_cb.value = self.exit_auto_stop_ledfx
        self.exit_all_off_auto_cb.value = self.exit_auto_all_off
        self.exit_ledfx_service_auto_cb.value = self.auto_start_ledfx_on_launch
        self.exit_wled_scene_auto_cb.value = self.auto_restore_wled_scene
        self.exit_ledfx_scene_auto_cb.value = self.auto_restore_ledfx_scene
        self.exit_status_text.value = ""

        self.exit_dialog.open = True
        self.page.update()

    def _confirm_app_close(self, e=None):
        self._exit_in_progress = True
        self._persist_exit_preferences(flush=True)
        self._on_exit_pref_change()
        if self.exit_auto_stop_ledfx:
            self._run_exit_stop_ledfx(auto=True)
        if self.exit_auto_all_off:
            self._run_exit_all_off(auto=True)
        self._close_exit_dialog()
        self._finalize_exit()

    def _finalize_exit(self):
        self.cleanup(None)
        try:
            win = self.page.window
            win.destroy()
            return
        except:
            pass
        try:
            self.page.window_destroy()
        except:
            pass
        
    def _find_ledfx_locally(self):
        """Search all internal fixed drives for ledfx.exe, ignoring USB/Removable."""
        possible_roots = []
        
        # 1. Get all internal fixed drives (HDD/SSD)
        try:
            for part in psutil.disk_partitions(all=False):
                # 'fixed' filters out USB sticks, CD-ROMs, and network drives
                if 'fixed' in part.opts:
                    # Look in "Program Files" and "Program Files (x86)" on every internal drive
                    possible_roots.append(os.path.join(part.mountpoint, "Program Files"))
                    possible_roots.append(os.path.join(part.mountpoint, "Program Files (x86)"))
        except:
            # Fallback to C: and D: if psutil fails to query partitions
            possible_roots.extend(["C:\\Program Files", "D:\\Program Files"])

        # 2. Add User-specific AppData paths (usually on C:)
        possible_roots.append(os.environ.get("LOCALAPPDATA", ""))
        possible_roots.append(os.environ.get("APPDATA", ""))

        # 3. Known sub-folders for LedFx
        sub_paths = [
            "LedFx\\ledfx.exe",
            "LedFx\\ledfx\\ledfx.exe",
            "Programs\\LedFx\\ledfx.exe", # LocalAppData variant
        ]

        self.log("Searching internal drives for LedFx...", color="blue400")

        for root in possible_roots:
            if not root or not os.path.exists(root):
                continue
            for sub in sub_paths:
                full_path = os.path.join(root, sub)
                if os.path.exists(full_path):
                    return full_path
        
        return None

    def _find_winamp_locally(self):
        """Find winamp.exe from running process or common install paths on internal drives."""
        # 1) If Winamp is already running, prefer its executable path.
        try:
            for _proc in psutil.process_iter(["name", "exe", "cmdline"]):
                _name = (_proc.info.get("name") or "").lower()
                if _name != "winamp.exe":
                    continue
                _exe = _proc.info.get("exe")
                if _exe and os.path.exists(_exe):
                    return _exe
                _cmd = _proc.info.get("cmdline") or []
                if _cmd and os.path.exists(_cmd[0]) and os.path.basename(_cmd[0]).lower() == "winamp.exe":
                    return _cmd[0]
        except Exception:
            pass

        # 2) Probe common install locations first.
        _candidate_paths = []
        for _base in [
            os.environ.get("PROGRAMFILES", ""),
            os.environ.get("PROGRAMFILES(X86)", ""),
            os.environ.get("LOCALAPPDATA", ""),
            os.environ.get("APPDATA", ""),
        ]:
            if not _base:
                continue
            _candidate_paths.append(os.path.join(_base, "Winamp", "winamp.exe"))
            _candidate_paths.append(os.path.join(_base, "Programs", "Winamp", "winamp.exe"))

        # 3) Scan likely folders on internal fixed drives.
        try:
            for _part in psutil.disk_partitions(all=False):
                if "fixed" not in (_part.opts or ""):
                    continue
                _mp = _part.mountpoint
                _candidate_paths.append(os.path.join(_mp, "Winamp", "winamp.exe"))
                _candidate_paths.append(os.path.join(_mp, "Program Files", "Winamp", "winamp.exe"))
                _candidate_paths.append(os.path.join(_mp, "Program Files (x86)", "Winamp", "winamp.exe"))
        except Exception:
            pass

        _seen = set()
        for _p in _candidate_paths:
            if not _p:
                continue
            _norm = self._normalize_path(_p)
            if _norm in _seen:
                continue
            _seen.add(_norm)
            if os.path.exists(_p):
                return _p
        return None
    
    def _find_spotify_exe_locally(self):
        """Find Spotify.exe from running process or common install paths."""
        try:
            for _proc in psutil.process_iter(["name", "exe", "cmdline"]):
                _name = (_proc.info.get("name") or "").lower()
                if _name != "spotify.exe":
                    continue
                _exe = _proc.info.get("exe")
                if _exe and os.path.exists(_exe):
                    return _exe
                _cmd = _proc.info.get("cmdline") or []
                if _cmd and os.path.exists(_cmd[0]) and os.path.basename(_cmd[0]).lower() == "spotify.exe":
                    return _cmd[0]
        except Exception:
            pass

        _candidate_paths = []
        _la = os.environ.get("LOCALAPPDATA", "")
        _ap = os.environ.get("APPDATA", "")
        if _la:
            _candidate_paths.append(os.path.join(_la, "Spotify", "Spotify.exe"))
            _candidate_paths.append(os.path.join(_la, "Microsoft", "WindowsApps", "Spotify.exe"))
        if _ap:
            _candidate_paths.append(os.path.join(_ap, "Spotify", "Spotify.exe"))
        for _base in [
            os.environ.get("PROGRAMFILES", ""),
            os.environ.get("PROGRAMFILES(X86)", ""),
        ]:
            if _base:
                _candidate_paths.append(os.path.join(_base, "Spotify", "Spotify.exe"))

        _seen = set()
        for _p in _candidate_paths:
            if not _p:
                continue
            _norm = self._normalize_path(_p)
            if _norm in _seen:
                continue
            _seen.add(_norm)
            if os.path.exists(_p):
                return _p
        return None

    def _set_spotify_exe_path_from_picker(self, key, path):
        """Persist selected Spotify.exe path for an existing Spotify exe card."""
        if not path:
            return
        info = self.custom_devices.get(key)
        if not isinstance(info, dict):
            return
        info["url"] = path
        info["is_exe"] = True
        self.custom_devices[key] = info
        c = self.cards.get(key)
        if c:
            c["_url"] = path
            c["_is_exe"] = True
        self.save_cache()
        _nm = c.get("name_label").value if c and c.get("name_label") else key
        self.log(f"[Spotify] Path set for '{_nm}': {path}", color="green400")

    def _show_spotify_exe_setup_dialog(self, key):
        """Show Spotify exe setup dialog when card path is missing or invalid."""
        c = self.cards.get(key, {})
        _nm = c.get("name_label").value if c.get("name_label") else key

        def _close(_=None):
            dlg.open = False
            try:
                self.page.update()
            except Exception:
                pass

        def _browse(_):
            _close()
            def _set_path(path):
                self._set_spotify_exe_path_from_picker(key, path)
            self._exe_pick_callback = _set_path
            self.exe_picker.pick_files(
                dialog_title="Select Spotify.exe",
                allowed_extensions=["exe"],
            )

        def _install_spotify(_):
            _close()
            threading.Thread(target=self._run_spotify_exe_install, args=(key,), daemon=True).start()

        def _open_downloads(_):
            _close()
            try:
                self.page.launch_url(SPOTIFY_DOWNLOADS_PAGE_URL)
            except Exception:
                pass

        dlg = ft.AlertDialog(
            title=ft.Text("Spotify Path Not Found"),
            content=ft.Column([
                ft.Text(f"Card '{_nm}' needs a valid Spotify.exe path.", size=12),
                ft.Text("Browse to your existing Spotify.exe, or open the download page.", size=12, color="grey500"),
            ], tight=True, spacing=8, width=420),
            actions=[
                ft.ElevatedButton("Install Spotify", icon=ft.Icons.DOWNLOAD_FOR_OFFLINE, bgcolor="green700", color="white", on_click=_install_spotify),
                ft.TextButton("Browse EXE", on_click=_browse),
                ft.TextButton("Open Download Page", on_click=_open_downloads),
                ft.TextButton("Cancel", on_click=_close),
            ],
        )
        self.page.overlay.append(dlg)
        dlg.open = True
        self.page.update()

    def _run_spotify_exe_install(self, key):
        """Download and launch Spotify setup exe, then auto-detect Spotify.exe path when available."""
        c = self.cards.get(key, {})
        _nm = c.get("name_label").value if c.get("name_label") else key
        installer_path = os.path.join(os.path.expanduser("~"), "SpotifySetup.exe")
        try:
            self.log(f"[Spotify] Downloading installer for '{_nm}'...", color="grey500")

            for _r, _pb, _pt in zip(self._progress_rows, self._progress_bars, self._percent_texts):
                _r.visible = True
                _pb.value = 0
                _pt.value = "0%"
                try:
                    _r.update()
                except Exception:
                    pass
            try:
                self.page.update()
            except Exception:
                pass

            with requests.get(SPOTIFY_SETUP_EXE_URL, stream=True, timeout=120) as r:
                r.raise_for_status()
                total = int(r.headers.get("content-length", 0))
                downloaded = 0
                last_pct = -1
                with open(installer_path, "wb") as f:
                    for chunk in r.iter_content(chunk_size=512 * 1024):
                        if not chunk:
                            continue
                        f.write(chunk)
                        downloaded += len(chunk)
                        if total > 0:
                            pct = int((downloaded / total) * 100)
                            if pct != last_pct and (pct % 5 == 0 or pct == 100):
                                last_pct = pct
                                _ratio = downloaded / total
                                for _r, _pb, _pt in zip(self._progress_rows, self._progress_bars, self._percent_texts):
                                    _pb.value = _ratio
                                    _pt.value = f"{pct}%"
                                    try:
                                        _r.update()
                                    except Exception:
                                        pass
                                try:
                                    self.page.update()
                                except Exception:
                                    pass

            self.log(f"[Spotify] Installer downloaded: {installer_path}", color="green400")
            os.startfile(installer_path)
            self.log("[Spotify] Installer launched. Auto-detecting Spotify.exe path...", color="orange400")

            _end = time.monotonic() + 90.0
            while self.running and (time.monotonic() < _end):
                _found = self._find_spotify_exe_locally()
                if _found and os.path.exists(_found):
                    self._set_spotify_exe_path_from_picker(key, _found)
                    self.log(f"[Spotify] Auto-detected install path for '{_nm}'", color="green400")
                    break
                time.sleep(1.0)
        except Exception as ex:
            self.log(f"[Spotify] Installer flow failed for '{_nm}': {ex}", color="red400")
        finally:
            for _r in self._progress_rows:
                _r.visible = False
                try:
                    _r.update()
                except Exception:
                    pass
            try:
                self.page.update()
            except Exception:
                pass
            self._schedule_installer_cleanup([installer_path], label="Spotify")

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

    def _set_winamp_path_from_picker(self, key, path):
        """Persist selected winamp.exe path for an existing Winamp custom card."""
        if not path:
            return
        info = self.custom_devices.get(key)
        if not isinstance(info, dict):
            return

        info["url"] = path
        info["is_exe"] = True
        self.custom_devices[key] = info

        c = self.cards.get(key)
        if c:
            c["_url"] = path
            c["_is_exe"] = True
            self._set_custom_card_media_text(key, self._get_winamp_now_playing_text())

        self.save_cache()
        _nm = c.get("name_label").value if c and c.get("name_label") else key
        self.log(f"[Winamp] Path set for '{_nm}': {path}", color="green400")

    def _show_winamp_setup_dialog(self, key):
        """Show Winamp setup dialog when card path is missing or invalid."""
        c = self.cards.get(key, {})
        _nm = c.get("name_label").value if c.get("name_label") else key

        def _close(_=None):
            dlg.open = False
            try:
                self.page.update()
            except Exception:
                pass

        def _browse(_):
            _close()

            def _set_path(path):
                self._set_winamp_path_from_picker(key, path)

            self._exe_pick_callback = _set_path
            self.exe_picker.pick_files(
                dialog_title="Select winamp.exe",
                allowed_extensions=["exe"],
            )

        def _install_legacy(_):
            _close()
            threading.Thread(target=self._run_winamp_legacy_install, args=(key,), daemon=True).start()

        def _open_downloads(_):
            _close()
            try:
                self.page.launch_url(WINAMP_DOWNLOADS_PAGE_URL)
            except Exception:
                pass

        dlg = ft.AlertDialog(
            title=ft.Text("Winamp Path Not Found"),
            content=ft.Column([
                ft.Text(f"Card '{_nm}' needs a valid winamp.exe path.", size=12),
                ft.Text("Choose Install Legacy or Browse to your existing winamp.exe.", size=12, color="grey500"),
            ], tight=True, spacing=8, width=420),
            actions=[
                ft.ElevatedButton("Install WINAMP", icon=ft.Icons.DOWNLOAD_FOR_OFFLINE, bgcolor="yellow700", color="black", on_click=_install_legacy),
                ft.TextButton("Browse EXE", on_click=_browse),
                ft.TextButton("Open Downloads Page", on_click=_open_downloads),
                ft.TextButton("Cancel", on_click=_close),
            ],
        )
        self.page.overlay.append(dlg)
        dlg.open = True
        self.page.update()

    def _run_winamp_legacy_install(self, key):
        """Download and launch official Winamp legacy installer, then prompt for final exe path."""
        c = self.cards.get(key, {})
        _nm = c.get("name_label").value if c.get("name_label") else key
        installer_path = os.path.join(os.path.expanduser("~"), "winamp_latest_full.exe")
        try:
            self.log(f"[Winamp] Downloading legacy installer for '{_nm}'...", color="grey500")

            # Reuse existing updater progress UI (same pattern used by LedFx download).
            for _r, _pb, _pt in zip(self._progress_rows, self._progress_bars, self._percent_texts):
                _r.visible = True
                _pb.value = 0
                _pt.value = "0%"
                try:
                    _r.update()
                except Exception:
                    pass
            try:
                self.page.update()
            except Exception:
                pass

            with requests.get(WINAMP_LEGACY_INSTALLER_URL, stream=True, timeout=120) as r:
                r.raise_for_status()
                total = int(r.headers.get("content-length", 0))
                downloaded = 0
                last_pct = -1
                last_kb = -1
                with open(installer_path, "wb") as f:
                    for chunk in r.iter_content(chunk_size=512 * 1024):
                        if chunk:
                            f.write(chunk)
                            downloaded += len(chunk)
                            if total > 0:
                                pct = int((downloaded / total) * 100)
                                if pct != last_pct and (pct % 5 == 0 or pct == 100):
                                    last_pct = pct
                                    self.log(f"[Winamp] Download {pct}%", color="grey500")
                                    _ratio = downloaded / total
                                    for _r, _pb, _pt in zip(self._progress_rows, self._progress_bars, self._percent_texts):
                                        _pb.value = _ratio
                                        _pt.value = f"{pct}%"
                                        try:
                                            _r.update()
                                        except Exception:
                                            pass
                                    try:
                                        self.page.update()
                                    except Exception:
                                        pass
                            else:
                                # Fallback when content-length is missing: show live KB counter.
                                _kb = int(downloaded / 1024)
                                if _kb - last_kb >= 256:
                                    last_kb = _kb
                                    for _r, _pb, _pt in zip(self._progress_rows, self._progress_bars, self._percent_texts):
                                        _pb.value = None
                                        _pt.value = f"{_kb} KB"
                                        try:
                                            _r.update()
                                        except Exception:
                                            pass
                                    try:
                                        self.page.update()
                                    except Exception:
                                        pass

            self.log(f"[Winamp] Installer downloaded: {installer_path}", color="green400")
            os.startfile(installer_path)
            self.log("[Winamp] Installer launched. After install, click Winamp card and browse to winamp.exe.", color="orange400")
        except Exception as ex:
            self.log(f"[Winamp] Installer download failed for '{_nm}': {ex}", color="red400")
        finally:
            for _r in self._progress_rows:
                _r.visible = False
                try:
                    _r.update()
                except Exception:
                    pass
            try:
                self.page.update()
            except Exception:
                pass
            self._schedule_installer_cleanup([installer_path], label="Winamp")

    def _schedule_installer_cleanup(self, paths, label="Installer"):
        """Best-effort deferred cleanup for downloaded installer/temp paths."""
        _paths = [p for p in (paths or []) if p]
        if not _paths:
            return

        def _worker(_paths_local, _label):
            # Give launched installer process a moment before first delete attempt.
            time.sleep(5)
            for _attempt in range(24):  # retry up to ~2 minutes
                _remaining = []
                for _p in _paths_local:
                    try:
                        if os.path.isdir(_p):
                            if os.path.exists(_p):
                                shutil.rmtree(_p)
                        else:
                            if os.path.exists(_p):
                                os.remove(_p)
                    except Exception:
                        _remaining.append(_p)
                if not _remaining:
                    self.log(f"[{_label}] Temp installer files cleaned up.", color="grey500")
                    return
                time.sleep(5)
            self.log(f"[{_label}] Could not clean some temp files yet:", color="orange400")
            for _p in _paths_local:
                if os.path.exists(_p):
                    self.log(f"[{_label}]   {_p}", color="grey500")

        threading.Thread(target=_worker, args=(_paths, label), daemon=True).start()

    def _launch_ledfx(self):
        """Start ledfx.exe and open the web UI once it is ready."""
        for _b in self._ledfx_btns:
            _b.disabled = True; _b.text = "STARTING..."; _b.bgcolor = "orange800"
            try: _b.update()
            except: pass
        self.log("[LedFx] Launching background process...")

        def _start():
            self._ledfx_launching = True
            cmd = [self.ledfx_path, "--clear-effects"]
            subprocess.Popen(cmd)
            #subprocess.Popen([self.ledfx_path])
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
                    self.log(f"LedFx: No path saved (latest: v{self.ledfx_latest_ver}) — use START LEDFX button, it will auto search path, prompt to install or browse to path")
                else:
                    self.log(f"LedFx: v{self.ledfx_current_ver} (up to date)")
        except: pass

    def _version_tuple(self, version_text):
        """Convert version string to comparable integer tuple, e.g. v4.5.9 -> (4, 5, 9)."""
        try:
            cleaned = (version_text or "").strip().lower().lstrip("v")
            nums = []
            cur = ""
            for ch in cleaned:
                if ch.isdigit():
                    cur += ch
                elif ch == ".":
                    if cur:
                        nums.append(int(cur))
                        cur = ""
                else:
                    if cur:
                        nums.append(int(cur))
                        cur = ""
            if cur:
                nums.append(int(cur))
            if not nums:
                return (0,)
            return tuple(nums)
        except:
            return (0,)

    def _is_newer_version(self, latest, current):
        latest_t = self._version_tuple(latest)
        current_t = self._version_tuple(current)
        # Pad tuples to equal length before compare: 4.5.9 == 4.5.9.0
        max_len = max(len(latest_t), len(current_t))
        latest_t += (0,) * (max_len - len(latest_t))
        current_t += (0,) * (max_len - len(current_t))
        return latest_t > current_t

    def _pick_wledcc_release_asset(self, assets):
        """Pick best Windows installer-like asset from release assets."""
        best = None
        best_score = -1
        for asset in assets or []:
            name = asset.get("name", "")
            url = asset.get("browser_download_url", "")
            if not name or not url:
                continue
            n = name.lower()

            # Skip clearly non-Windows/source artifacts.
            if "source code" in n or n.endswith(".sig") or n.endswith(".sha256"):
                continue
            if any(tok in n for tok in ["linux", "mac", "darwin", "arm64", "aarch64"]):
                continue
            if not (n.endswith(".exe") or n.endswith(".msi") or n.endswith(".zip")):
                continue

            score = 0
            if n.endswith(".exe"):
                score += 60
            elif n.endswith(".msi"):
                score += 55
            elif n.endswith(".zip"):
                score += 35

            if "setup" in n or "installer" in n:
                score += 40
            if "win" in n or "windows" in n:
                score += 20
            if "x64" in n or "amd64" in n:
                score += 10
            if "portable" in n:
                score -= 10

            if score > best_score:
                best_score = score
                best = asset

        return best

    def _pick_latest_wledcc_release_payload(self, releases):
        """Pick highest-version non-draft, non-prerelease release payload from GitHub list."""
        try:
            best = None
            best_ver = (0,)
            best_pub = ""
            for rel in releases or []:
                if not isinstance(rel, dict):
                    continue
                if rel.get("draft") or rel.get("prerelease"):
                    continue
                tag = (rel.get("tag_name") or "").strip()
                if not tag:
                    continue
                ver = self._version_tuple(tag)
                pub = (rel.get("published_at") or "").strip()
                if (ver > best_ver) or (ver == best_ver and pub > best_pub):
                    best = rel
                    best_ver = ver
                    best_pub = pub
            return best
        except:
            return None

    def _find_installer_in_extracted_zip(self, extract_path):
        """Find best installer candidate inside extracted zip folder."""
        best = None
        best_score = -1
        for root, _, files in os.walk(extract_path):
            for fname in files:
                n = fname.lower()
                if not (n.endswith(".exe") or n.endswith(".msi")):
                    continue
                full = os.path.join(root, fname)
                score = 0
                if n.endswith(".exe"):
                    score += 50
                elif n.endswith(".msi"):
                    score += 45
                if "setup" in n or "installer" in n:
                    score += 40
                if "wledcc" in n:
                    score += 20
                if score > best_score:
                    best_score = score
                    best = full
        return best

    def _bring_window_to_front(self, title_hints, timeout_sec=10):
        """Try to bring a newly launched installer window to the foreground (Windows)."""
        hints = [h.lower() for h in (title_hints or []) if h]
        if not hints:
            return False

        deadline = time.time() + max(1, int(timeout_sec))
        while time.time() < deadline:
            matches = []

            def _enum_cb(hwnd, _):
                try:
                    if not win32gui.IsWindowVisible(hwnd):
                        return True
                    title = (win32gui.GetWindowText(hwnd) or "").strip()
                    if not title:
                        return True
                    t = title.lower()
                    if any(h in t for h in hints):
                        matches.append(hwnd)
                except:
                    return True
                return True

            try:
                win32gui.EnumWindows(_enum_cb, None)
            except:
                return False

            if matches:
                hwnd = matches[0]
                try:
                    if win32gui.IsIconic(hwnd):
                        win32gui.ShowWindow(hwnd, win32con.SW_RESTORE)
                    # Topmost toggle helps force z-order above this app.
                    win32gui.SetWindowPos(
                        hwnd, win32con.HWND_TOPMOST, 0, 0, 0, 0,
                        win32con.SWP_NOMOVE | win32con.SWP_NOSIZE
                    )
                    win32gui.SetWindowPos(
                        hwnd, win32con.HWND_NOTOPMOST, 0, 0, 0, 0,
                        win32con.SWP_NOMOVE | win32con.SWP_NOSIZE
                    )
                    win32gui.SetForegroundWindow(hwnd)
                    return True
                except:
                    pass

            time.sleep(0.2)

        return False

    def install_or_update_wledcc(self, e=None):
        if not self.wledcc_download_url:
            self.log("[WLEDCC] No installer asset found in latest release. Opening releases page.", color="orange400")
            try:
                self.page.launch_url(WLEDCC_RELEASES_PAGE_URL)
            except:
                pass
            return
        self.wledcc_update_btn.disabled = True
        self.wledcc_update_btn.text = "DOWNLOADING..."
        self.wledcc_update_btn.bgcolor = "orange700"
        try: self.wledcc_update_btn.update()
        except: pass
        self._open_log()
        threading.Thread(target=self._run_wledcc_install, daemon=True).start()

    def _run_wledcc_install(self):
        asset_name = self.wledcc_asset_name or "wledcc_update.bin"
        download_path = os.path.join(os.path.expanduser("~"), asset_name)
        extract_path = os.path.join(os.path.expanduser("~"), "wledcc_update_tmp")
        try:
            self.log(f"[WLEDCC] Downloading {asset_name}...")
            with requests.get(self.wledcc_download_url, stream=True, timeout=120) as r:
                r.raise_for_status()
                total = int(r.headers.get("content-length", 0))
                downloaded = 0
                last_pct = -1
                with open(download_path, "wb") as f:
                    for chunk in r.iter_content(chunk_size=512 * 1024):
                        if not chunk:
                            continue
                        f.write(chunk)
                        downloaded += len(chunk)
                        if total > 0:
                            pct = int((downloaded / total) * 100)
                            if pct != last_pct and (pct % 5 == 0 or pct == 100):
                                last_pct = pct
                                self.wledcc_update_btn.text = f"DOWNLOADING {pct}%"
                                try: self.wledcc_update_btn.update()
                                except: pass

            target = download_path
            lower_name = asset_name.lower()
            if lower_name.endswith(".zip"):
                self.log("[WLEDCC] Extracting update package...")
                if os.path.exists(extract_path):
                    shutil.rmtree(extract_path)
                with zipfile.ZipFile(download_path, "r") as zf:
                    zf.extractall(extract_path)
                target = self._find_installer_in_extracted_zip(extract_path)
                if not target:
                    raise RuntimeError("No installer executable found inside zip")

            self.log(f"[WLEDCC] Launching installer: {os.path.basename(target)}", color="yellow700")
            self.log("[WLEDCC] Close WLED COMMAND CENTER before Update / Install.", color="red400")
            os.startfile(target)
            installer_base = os.path.splitext(os.path.basename(target))[0]
            brought_front = self._bring_window_to_front(
                [installer_base, "wledcc", "setup", "installer"],
                timeout_sec=8,
            )
            if not brought_front:
                self.log("[WLEDCC] Installer launched, but could not force it to front.", color="orange400")

            self.wledcc_update_btn.text = "INSTALLER OPENED"
            self.wledcc_update_btn.bgcolor = "green700"
            self.wledcc_update_btn.disabled = True
            try: self.wledcc_update_btn.update()
            except: pass
        except Exception as ex:
            self.log(f"[WLEDCC] Update failed: {ex}", color="red400")
            self.wledcc_update_btn.disabled = False
            self.wledcc_update_btn.bgcolor = "yellow700"
            if self.wledcc_latest_ver:
                self.wledcc_update_btn.text = f"UPDATE TO v{self.wledcc_latest_ver}"
            else:
                self.wledcc_update_btn.text = "UPDATE APP"
            try: self.wledcc_update_btn.update()
            except: pass
        finally:
            self._schedule_installer_cleanup([download_path, extract_path], label="WLEDCC")

    def check_wledcc_updates(self):
        try:
            self.log(f"[WLEDCC] Checking for app updates... (current v{APP_VERSION})", color="cyan")
            payload = None

            # Prefer releases list and pick highest version ourselves.
            # GitHub /releases/latest can occasionally lag behind newly published releases.
            try:
                list_resp = requests.get(WLEDCC_RELEASES_LIST_URL, timeout=10)
                if list_resp.status_code == 200:
                    rels = list_resp.json()
                    if isinstance(rels, list):
                        payload = self._pick_latest_wledcc_release_payload(rels)
                else:
                    self.log(f"[WLEDCC] Releases list HTTP status: {list_resp.status_code}", color="orange400")
            except Exception as ex:
                self.log(f"[WLEDCC] Releases list fetch failed: {ex}", color="orange400")

            if not payload:
                resp = requests.get(WLEDCC_RELEASES_API_URL, timeout=10)
                if resp.status_code != 200:
                    self.log(f"[WLEDCC] Update check HTTP status: {resp.status_code}", color="orange400")
                    return
                payload = resp.json()

            latest_tag = payload.get("tag_name", "").strip()
            latest_clean = latest_tag.lstrip("vV")
            current_clean = (APP_VERSION or "").strip().lstrip("vV")
            self.wledcc_latest_ver = latest_clean
            picked = self._pick_wledcc_release_asset(payload.get("assets", []))
            self.wledcc_download_url = picked.get("browser_download_url") if picked else None
            self.wledcc_asset_name = picked.get("name") if picked else None

            if self._is_newer_version(latest_clean, current_clean):
                self.log(f"WLEDCC update available: v{current_clean} -> v{latest_clean}", color="yellow700")
                if self.wledcc_asset_name:
                    self.log(f"[WLEDCC] Using release asset: {self.wledcc_asset_name}", color="grey500")
                else:
                    self.log("[WLEDCC] No installable asset found; button will open releases page.", color="orange400")
                self.wledcc_update_btn.visible = True
                self.wledcc_update_btn.text = f"UPDATE TO v{latest_clean}"
                self.wledcc_update_btn.tooltip = f"Download and install WLEDCC v{latest_clean}"
                try: self.wledcc_update_btn.update()
                except: pass
            else:
                self.log(f"WLEDCC: v{current_clean} (up to date)", color="grey500")
        except Exception as ex:
            self.log(f"WLEDCC update check failed: {ex}", color="orange400")

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

    def _on_exe_pick_result(self, e: ft.FilePickerResultEvent):
        """Called when user browses to an EXE in the Add Device dialog."""
        if e.files and self._exe_pick_callback:
            self._exe_pick_callback(e.files[0].path)
        self._exe_pick_callback = None

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
        # Intercept window close so we can show exit options first.
        try:
            win = self.page.window
            win.prevent_close = True
            win.on_event = self.handle_window_event
        except AttributeError:
            try:
                self.page.window_prevent_close = True
                self.page.on_window_event = self.handle_window_event
            except:
                pass
        
        def _manual_line(line, prev_line="."):
            import re as _re
            # Only color leading ALL-CAPS tokens when the previous line ended with "."
            # — that signals this line starts a new feature entry, not a mid-paragraph cap.
            m = _re.match(r"^(\s*)(.*)$", line)
            left_pad = m.group(1)
            body = m.group(2)
            cap_token = _re.compile(r"^[A-Z0-9/&()+.'-]+$")
            lead_count = 0
            if prev_line.rstrip().endswith("."):
                tokens = body.split(" ")
                for t in tokens:
                    if t and cap_token.match(t):
                        lead_count += 1
                        continue
                    break
                if lead_count > 0:
                    lead = " ".join(tokens[:lead_count])
                    rest = body[len(lead):]
                    return ft.Row([
                        ft.Text(f"{left_pad}{lead}", size=12, color="#8ea3b5", no_wrap=True),
                        ft.Text(rest, size=12, color="grey300", expand=True),
                    ], spacing=0, tight=True)
            return ft.Text(line, size=12, color="grey300")

        def _section(title, color, *lines):
            controls = [
                ft.Container(height=6),
                ft.Text(title, weight="bold", color=color, size=13),
            ]
            prev = "."  # treat section start as a fresh sentence so first line qualifies
            for l in lines:
                controls.append(_manual_line(l, prev))
                prev = l.rstrip()
            return controls

        manual_content = ft.Column(
            scroll=ft.ScrollMode.AUTO,
            width=520,
            height=520,
            spacing=2,
            controls=[
                #ft.Text("WLED COMMAND CENTER+ — USER MANUAL", weight="bold", size=14, color="#00f2ff"),
                ft.TextButton(
                    content=ft.Text("by SullySSignS.ca", size=10, color="grey600"),
                    on_click=lambda _: self.page.launch_url("https://www.sullyssigns.ca"),
                    tooltip="Visit sullyssigns.ca",
                    style=ft.ButtonStyle(padding=ft.padding.only(top=0, bottom=0)),
                ),
                ft.Divider(),

                *_section("NEW FEATURES Added in V4.6.7", "#ff9800",
                    "SPECTRUM ANALYZER (PC AUDIO)",
                    "The header includes a live spectrum analyzer that reacts to your PC audio.",
                    "Click the spectrum display or MIC icon to open Spectrum Settings.",
                    "",
                    "SPECTRUM SETTINGS (MODES + TUNING).",
                    "SENSITIVITY — Global analyzer gain.",
                    "REACTIVITY — How fast bars rise on transients.",
                    "BAR DECAY — How fast bars fall.",
                    "PEAK DECAY — How fast peak markers fall.",
                    "MODE — Classic, VU (L/R), Random (1 min), Random (Per Song).",
                    "IDLE EFFECTS — Runs ambient visuals after silence timeout.",
                    "IDLE EFFECT OPTIONS — Pac-Man, Tetris, Invaders, Snake and more.",
                    "",
                    "SPECTRUM VISUAL EQ (UI ONLY)",
                    "10-band visual EQ is available in Spectrum Settings.",
                    "Presets: Flat, Bass+, Smile, Vocal.",
                    "Important: This EQ only changes the analyzer visualization in WLEDCC.",
                    "It does not change Windows audio output or device audio tone. (yet)",
                    "",
                    "LEDFX SCENES MODE",
                    "Scene bar can switch between WLED scenes and LedFx scenes.",
                    "Use the scene mode toggle button in the scene bar.",
                    "When LedFx mode is selected, WLEDCC fetches current scenes from LedFx.",
                    "If no scenes are returned, the row shows \"No LedFx scenes\".",
                    "",
                    "EXIT POPUP AUTOMATION (BEFORE CLOSING APP)",
                    "Auto-run on exit options let you save one-click shutdown behavior:",
                    "- Stop LedFx automatically on exit.",
                    "- Run All Lights Off automatically on exit.",
                    "Startup automation options are also saved here:",
                    "- Auto-start LedFx on app launch.",
                    "- Auto-load last WLED scene.",
                    "- Auto-load last LedFx scene.",
                    "",
                    "CUSTOM CARD AUTOMATION",
                    "Custom cards now include per-card automation checkboxes.",
                    "- AUTO START: launches this card target when WLEDCC starts.",
                    "- AUTO CLOSE / STOP ON EXIT: closes target when WLEDCC exits.",
                    "",
                    "SPOTIFY WEB CARD CONTROLS",
                    "Spotify web cards show controls for:",
                    "- Previous",
                    "- Play/Pause",
                    "- Next",
                    "- Show Spotify Web UI",
                    "Status line can show now-playing style feedback when available.",
                    "",
                    "WINAMP CARD CONTROLS + SETUP",
                    "Winamp cards include controls for:",
                    "- Previous, Play, Pause, Stop, Next",
                    "If winamp.exe path is missing, WLEDCC offers:",
                    "- Install WINAMP (legacy installer)",
                    "- Browse to existing winamp.exe",
                    "- Open Winamp downloads page",
                    "",
                    "DEFAULT QUICK CARDS",
                    "On first run, WLEDCC will add default custom cards:",
                    "- WINAMP",
                    "- SPOTIFY.COM",
                    "",
                    "EDIT DEVICE IP",
                    "Device IP can be edited directly from the card IP field.",
                    "WLEDCC rebinds the device live to the new IP.",
                    "Note: some controls may require app restart for full re-bind.",
                    "",
                    "LOG OPTIONS EXPANDED",
                    "OPEN LOG now includes additional options:",
                    "- DBG on open (turn debug on when log opens)",
                    "- Auto-open (open log panel at app startup)",
                    "- Save to disk (write current session logs to file)",
                    "- BG updates (continue log/UI updates when app is not focused)",
                    "",
                    "BUG FIXES",
                    "- Brightness sliders were not showing numberical value.",
                    "- Devices now remember last color\\brightness between sessions",
                    "- Reduced logs to one per session, 10 Max",
                    "- Last used scene button border now glows",
                    "",
                    "",
                ),

                *_section("WHAT IS THIS PROGRAM?", "#00f2ff",
                    "WLED COMMAND CENTER+ lets you control all your WLED, LEDFX, MagicHome, and",
                    "custom devices from one place. Devices are auto-discovered on startup.",
                    "It checks for new firmware for all your Devices and provides one click ",
                    "automatic installs.  All settings, names, scenes and card order are saved",
					"and restored between sessions.  Reboot slow devices, Sanitize Presets,",
					"record/play presets/scenes for WLED and LEDFX.  Access WLED and LEDFX",
					"WED UI's right from inside this program.  Make custom Cards for your",
					"favorite WEB SITES, Program EXE's, etc and all from one screen.",
                    "Setup automatic actions — like starting/stopping LEDFX or turning lights on/off. ",
                    "Even Auto start and close for your favorite music apps or WEB SITES ",
                    "with custom CARDS on the main screen.",
					"Truely a ALL-IN-ONE Control Center for your music room.",
                ),
				
				*_section("APP NAME BAR", "cyan",
                    "SLIDERS - Use to control SPEED or BRIGHTNESS for APP NAME and CARDS.",
					"LEFT CONTROLS - APP NAME.", \
                    "RIGHT CONTROLS - Device CARDS.",
					"COLOR PICKERS - changes color for solid or breathing effects.",
					"EFFECT PICKERS - changes effects - rainbow, solid, wave, etc.",
					"SCAN — Refreshes device status and looks for newly found devices.",
                    "Use this after a router reboot or when a device changes IP.",
				),	

                *_section("TOP BAR — GLOBAL CONTROLS", "cyan",
                    "ALL OFF / ALL ON — One-click control to toggle every light in the house.",
                    "OPEN LOG — Opens a message panel at the TOP of the app.",
					"AUTO-SCROLL ON/OFF keeps window focused on recent messages.",
                    "COPY LOG copies the text.",
					"CLEAR LOG clears the messages.",
					"only clears the screen, logs still saved to file.",
					"OPEN FOLDER opens to saved logs and config folder.",
                    "DEBUG ON/OFF shows extra troubleshooting details.",
					"DBG / AUTO OPEN check boxs to have log auto open in DEBUG mode.",
					"CLOSE LOG hides this window.",
					"While window is open, use grab bar botton center to size it.",
					"MANUAL — Opens this guide.",
                    "MERGE — attempts to fix duplicate cards.  Use this if device appears twice.",
					"keeps ID so device is linked to scenes/presets still.  (WIP).",
                    "click MERGE, then drag the new card onto the old one.",
                    "Click MERGE again to cancel.",
                    "MASTER BRIGHTNESS — Dim or brighten all lights at once while keeping",
					"their brightness levels relative to each other. (WIP).",
                    "SCENES — Your saved scene buttons live here. See SCENES below.",
                    "START LEDFX / STOP LEDFX — Starts or stops LedFx service.",
					"Prompts for INSTALL/UPDATE/BROWSE for path if not found.",
                    "LEDFX UI — Opens the LedFx web UI when LedFx is running.",
                ),

                *_section("DEVICE CARDS", "cyan",
                    "Each device gets its own card showing name, type badge, IP,",
                    "firmware version, chip type, WiFi signal, current effect and more.",
                    "Cards glow rainbow when on, dim when off, red when offline.",
                    "WLED cards show a cyan WLED badge. Click it to open WLED's WEB UI.",
					"MAGICHOME cards show a green MH badge.",
                    "DRAG HANDLE (⠿) — Left edge of card. Drag to reorder.",
                    "MERGE mode, dropping onto another card offers Reorder or Merge.",
                    "RENAME — Pencil icon. Give the device a friendly name.",
                    "REMOVE — Red X removes a dead or unwanted card. If the device",
                    "is still on the network it will reappear automatically on next scan.",
                    "POWER SWITCH — Toggles device on or off.",
                    "BRIGHTNESS SLIDER — Adjusts brightness in color mode, or controls",
                    "effect speed in MagicHome effect mode.",
                    "COLOR — Rainbow button opens a color picker.",
                    "PRESET / MODES — Opens saved presets (WLED) or built-in effects (MH)",
                ),

                *_section("WLED-ONLY CONTROLS", "#00f2ff",
                    "OPEN WEB UI — Click the WLED badge to open the full WLED web UI.",
                    "SANITIZE — Strips brightness from saved presets so switching presets",
                    "no longer changes your brightness unexpectedly.",
                    "Close the WLED web UI before running to avoid corrupt presets.",
                    "UPDATE — Appears when newer firmware is available. One click, downloads,",
                    "UnZips, and flashes the correct stable build for your device.",
                    "LIVE BADGES — Appear on all WLED cards whenever LedFx is running.",
                    "PURPLE badge — LedFx currently has control of this device.",
					"GREY badge, WLED has control.",
					"click badges to toggle LEDFX/WLED control.",
					"Color and preset controls are locked during LEDFX control.",
					"Power/brightness still work.",
					"Off devices that LEDFX takes control of, keep power switch off, ",
					"so once LEDFX releases control, device returns to off automatically.",
					"Cards that were ON before LEDFX took control, stay on after.",
                    "Badges hide automatically when LedFx service is stopped.",
                ),

                *_section("MAGICHOME NOTES", "#00ff88",
                    "MagicHome devices support color and built-in effects only.",
                    "No Sanitize or firmware update — those are WLED features.",
                    "COLOR PICKER changes switch back to static mode automatically.",
                    "EFFECTS PICKER lets you select from 21 built-in patterns.",
                    "BRIGHTNESS SLIDER — works in static color mode. In effect mode, slider = speed.",
                    "POWER ON VIA SLIDER — If the device is off and you move the brightness",
                    "slider or pic a color, the device powers on automatically.",
                ),

                *_section("SCENES", "cyan",
                    "Scene buttons sit in the master bar. You always see your saved scenes",
                    "plus one ADD button. There is no limit — record as many as you need.",
                    "Each scene stores the full state of every device — on/off, brightness,",
                    "color, effect, and active WLED preset. Scenes use a stable internal ID",
                    "so they survive device IP changes and renames.",
                    "ADD SCENE (+) — Click empty slot to snapshot all devices now.",
                    "Name the scene and press Enter or Save.",
					"EDIT — Right hamburger icon opens the scene editor.",
                    "Check a box to include a device. Uncheck it to ignore that device.",
                    "Use the refresh button beside a device to re-save only that device's",
                    "current state without recording the whole scene again.",					
                    "ACTIVATE — Click the scene name to play this scene.",
                    "RENAME — Left pencil icon on scene button to change its name.",
                    "CLEAR — X icon deletes the scene slot.",
                    "Scenes are saved to disk and survive restarts.",
                ),

                *_section("LEDFX AUDIO SYNC", "purple",
					"Turn your lights into a visualizer that react to your computer's audio.",
					"If path not found, clicking start prompts you to install",
					"or browse to path where you have it installed.",
					"Install downloads and installs automatically when clicked.",
                    "START LEDFX — Launches LedFx service. Adds Purple LIVE badge to Card.",
                    "STOP LEDFX — Shuts down LedFx. Unlocks WLED controls.  Removes badge.",
                    "LEDFX UI — Opens the LedFx web interface in your browser. Only",
                    "visible while LedFx is running, beside the STOP LEDFX button.",
                    "LIVE MODE — While LedFx runs, all WLED cards show a LIVE badge.",
                    "This lets you see which lights LedFx is controlling right now.",
                    "PURPLE LIVE badge — LedFx is actively controlling this device.",
                    "Click to release it back to WLED. Badge turns grey.",
                    "GREY LIVE badge — LedFx is running but not controlling this device.",
                    "Click it to have LedFx control it. Badge turns purple.",
                    "All badges hide when LedFx is stopped.",
                ),

             *_section("ADDING CUSTOM DEVICES", "cyan",
					"This allows you to add custom cards to launch almost anything.",
                    "ADD DEVICE card is always last in the grid.",
                    "Click it and enter IP address, web URL or path to program files.",
                    "IP ADDRESS — app probes for WLED, then TCP on port 80.",
                    "If WLED found: adds a full WLED card automatically.",
                    "HOSTNAME (e.g. house.local) — creates a launcher card.",
                    "URL (e.g. spotify.com) — launches URL in browser.",
                    "EXE - browse to your favorite program exe and it adds a launch button.",
                ),
				
                *_section("CLOSING THE APP", "cyan",
                    "When you click the X to close the app, a closing popup appears first.",
                    "STOP LEDFX — Stops LedFx before you leave the app.",
                    "ALL OFF — Turns all lights off before you leave the app.",
                    "CLOSE App — Exits the app.",
                    "CANCEL — Closes the popup and returns to the app.",
                    "CHECK BOXES — allow you to set LedFX to shut down when app closes.",
                    "Set lights to turn off on app close.",
                    "Auto load last scene when app opens.",
                ),

                *_section("TROUBLESHOOTING & NETWORK", "cyan",
					"The app automatically scans for devices on first start up.",
					"Run it again anytime by clicking SCAN button, top right of screen.",
					"MOVED DEVICES — If a light stops responding because your router gave it",
					"a new address, click SCAN. The app will usually find it and update",
					"your existing card automatically.",
					"DUPLICATE CARDS — If a device appears twice, click MERGE and drag",
					"the 'new' card onto your 'old' card. This keeps your custom names",
					"and scenes intact while updating the connection info. (WIP)",
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
        self.save_logs_to_disk_cb = ft.Checkbox(
            label="Save to disk",
            value=self.save_logs_to_disk,
            label_style=ft.TextStyle(size=9, color="grey500"),
            on_change=self._on_save_logs_to_disk_change,
            scale=0.8,
            tooltip="When checked, log lines are written to a single session log file",
        )
        self.unfocused_updates_cb = ft.Checkbox(
            label="BG updates",
            value=self.unfocused_updates_enabled,
            label_style=ft.TextStyle(size=9, color="grey500"),
            on_change=self._on_unfocused_updates_change,
            scale=0.8,
            tooltip="When checked, Log and UI updates continue while the app is out of focus",
        )
        self.log_options_btn = ft.PopupMenuButton(
            icon=ft.Icons.TUNE,
            tooltip="Log options",
            items=[
                ft.PopupMenuItem(content=self.debug_on_open_cb),
                ft.PopupMenuItem(content=self.log_auto_open_cb),
                ft.PopupMenuItem(content=self.unfocused_updates_cb),
                ft.PopupMenuItem(content=self.save_logs_to_disk_cb),
            ],
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
                    ft.Row([ft.Text("DEBUG CONSOLE", size=10, weight="bold", color="grey600"), self.autoscroll_btn, self.copy_log_btn, self.clear_log_btn, self.open_folder_btn, self.debug_btn, self.log_options_btn], spacing=6, vertical_alignment=ft.CrossAxisAlignment.CENTER),
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
            height=30,
            style=ft.ButtonStyle(
                shape=ft.RoundedRectangleBorder(radius=6),
                side=ft.BorderSide(1, "#2b2b3b"),
            ),
        )
        # ledfx buttons — two instances each so both wide and narrow layouts stay in sync
        self.ledfx_btn_wide   = ft.ElevatedButton("START LEDFX", icon=ft.Icons.EQUALIZER, color="white", bgcolor="purple700", on_click=self.toggle_ledfx, height=36)
        self.ledfx_btn_narrow = ft.ElevatedButton("START LEDFX", icon=ft.Icons.EQUALIZER, color="white", bgcolor="purple700", on_click=self.toggle_ledfx, height=36)
        self.ledfx_ui_btn_wide   = ft.ElevatedButton("LEDFX UI", icon=ft.Icons.OPEN_IN_BROWSER, color="white", bgcolor="purple900", visible=False, on_click=lambda _: self.page.launch_url("http://localhost:8888/#/devices"), height=36)
        self.ledfx_ui_btn_narrow = ft.ElevatedButton("LEDFX UI", icon=ft.Icons.OPEN_IN_BROWSER, color="white", bgcolor="purple900", visible=False, on_click=lambda _: self.page.launch_url("http://localhost:8888/#/devices"), height=36)
        self.scene_toggle_btn_wide   = ft.ElevatedButton("LEDFX SCENES", icon=ft.Icons.SWAP_HORIZ, color="white", bgcolor="purple900", visible=False, on_click=self.toggle_scene_mode, height=36)
        self.scene_toggle_btn_narrow = ft.ElevatedButton("LEDFX SCENES", icon=ft.Icons.SWAP_HORIZ, color="white", bgcolor="purple900", visible=False, on_click=self.toggle_scene_mode, height=36)
        self.wledcc_update_btn = ft.ElevatedButton(
            "UPDATE APP",
            icon=ft.Icons.SYSTEM_UPDATE_ALT,
            color="black",
            bgcolor="yellow700",
            visible=False,
            height=20,
            style=ft.ButtonStyle(padding=ft.padding.symmetric(horizontal=6, vertical=0)),
            on_click=self.install_or_update_wledcc,
        )
        self.ledfx_update_btn_wide   = ft.ElevatedButton("UPDATE LEDFX", icon=ft.Icons.DOWNLOAD_FOR_OFFLINE, color="black", bgcolor="yellow700", visible=False, on_click=self.install_or_update_ledfx)
        self.ledfx_update_btn_narrow = ft.ElevatedButton("UPDATE LEDFX", icon=ft.Icons.DOWNLOAD_FOR_OFFLINE, color="black", bgcolor="yellow700", visible=False, on_click=self.install_or_update_ledfx)
        self.update_progress_bar = ft.ProgressBar(value=0, width=260, color="yellow700", bgcolor="#2b2b3b")
        self.update_percent_text = ft.Text("0%", size=10, color="yellow700")
        self.update_progress_label = ft.Text("DOWNLOAD", size=10, color="yellow700", weight="bold")
        self.update_progress_row = ft.Row(
            [self.update_progress_label, self.update_progress_bar, self.update_percent_text],
            visible=False,
            spacing=10,
            alignment=ft.MainAxisAlignment.CENTER,
        )
        # Convenience lists for broadcasting state to both layouts at once
        self._ledfx_btns        = [self.ledfx_btn_wide,          self.ledfx_btn_narrow]
        self._ledfx_ui_btns     = [self.ledfx_ui_btn_wide,       self.ledfx_ui_btn_narrow]
        self._scene_toggle_btns = [self.scene_toggle_btn_wide,   self.scene_toggle_btn_narrow]
        self._ledfx_update_btns = [self.ledfx_update_btn_wide,   self.ledfx_update_btn_narrow]
        self._progress_bars     = [self.update_progress_bar]
        self._percent_texts     = [self.update_percent_text]
        self._progress_rows     = [self.update_progress_row]
        

        # Build per-character title controls before the header Row so they
        # can be referenced inline without statements inside a list literal.
        self._title_chars = []
        for _ch in "WLED COMMAND CENTER+":
            self._title_chars.append(
                ft.Text(_ch, size=28, weight="bold", italic=True, color="#00f2ff")
            )

        # ── Title animation controls (near SullySigns) ───────────────────────
        self._title_speed_slider = ft.Slider(
            min=2, max=20, value=self.title_speed, width=160,
            active_color="cyan",
            on_change=lambda e: (setattr(self, "title_speed", float(e.control.value)), self.save_cache()),
        )
        _title_color_btn = ft.Container(
            width=28, height=28, border_radius=6,
            gradient=ft.LinearGradient(
                begin=ft.alignment.top_left, end=ft.alignment.bottom_right,
                colors=["#FF0000","#FF8800","#FFFF00","#00FF00","#00FFFF","#0000FF","#FF00FF","#FF0000"],
            ),
            tooltip="Title color",
            ink=True, on_click=lambda _: self.show_anim_color_picker("title"),
        )
        _title_effect_btn = ft.Container(
            width=28, 
            height=28, 
            border_radius=6,
            bgcolor="#1e2133",
            border=ft.border.only(top=ft.border.BorderSide(1, "white10")), 
            shadow=[
                ft.BoxShadow(
                    blur_radius=10, 
                    color=ft.Colors.with_opacity(0.4, "black")
                )
            ],
            tooltip="Title effect", 
            ink=True,
            on_click=lambda _: self.show_anim_effect_picker("title"),
            content=ft.Icon(ft.Icons.AUTO_AWESOME, size=14, color="#00f2ff"), # Note: use ft.icons (lowercase 'i')
        )

        # ── Border animation controls (near SCAN) ─────────────────────────────
        self._border_speed_slider = ft.Slider(
            min=2, max=20, value=self.border_speed, width=160,
            active_color="cyan",
            on_change=lambda e: (setattr(self, "border_speed", float(e.control.value)), self.save_cache()),
        )
        _border_color_btn = ft.Container(
            width=28, height=28, border_radius=6,
            gradient=ft.LinearGradient(
                begin=ft.alignment.top_left, end=ft.alignment.bottom_right,
                colors=["#FF0000","#FF8800","#FFFF00","#00FF00","#00FFFF","#0000FF","#FF00FF","#FF0000"],
            ),
            tooltip="Border color",
            ink=True, on_click=lambda _: self.show_anim_color_picker("border"),
        )
        #ppp
        _border_effect_btn = ft.Container(
            width=28, 
            height=28, 
            border_radius=6,
            bgcolor="#1e2133",
            border=ft.border.only(top=ft.border.BorderSide(1, "white10")), 
            shadow=[
                ft.BoxShadow(
                    blur_radius=10, 
                    color=ft.Colors.with_opacity(0.4, "black")
                )
            ],
            tooltip="Border effect", 
            ink=True,
            on_click=lambda _: self.show_anim_effect_picker("border"),
            content=ft.Icon(ft.Icons.AUTO_AWESOME, size=14, color="#00f2ff"),
        )
#ppp
        self._title_meta_row = ft.Row([
            ft.Row(self._title_chars, spacing=0, tight=True),
            ft.Text(f"v{APP_VERSION}", size=10, color="grey600"),
            ft.TextButton(
                content=ft.Text("by SullySSignS.ca", size=10, color="grey600"),
                on_click=lambda _: self.page.launch_url("https://www.sullyssigns.ca"),
                tooltip="Visit sullyssigns.ca",
                style=ft.ButtonStyle(padding=ft.padding.all(0)),
            ),
        ], vertical_alignment="end", spacing=6)

        self._title_anim_row = ft.Row([
            self._title_speed_slider,
            _title_color_btn,
            _title_effect_btn,
        ], spacing=4, vertical_alignment=ft.CrossAxisAlignment.END)
        self._title_anim_wrap = ft.Container(
            content=self._title_anim_row,
            padding=ft.padding.only(top=0),
        )

        # ── Winamp-style spectrum analyzer (in header gap) ───────────────────
        _spec_palette = [
            "#00a800", "#00b500", "#00c300", "#00d000", "#00dd00", "#22e000",
            "#4de200", "#7ae400", "#a8e600", "#d6dd00", "#f0c400", "#f59f00",
            "#f97800", "#fb4f00", "#fd2d00", "#ff0000",
        ]
        self._spec_segments = []
        _band_controls = []
        for _ in range(self._spec_bands):
            _levels = []
            for _lvl in range(self._spec_levels):
                _c = ft.Container(
                    width=7,
                    height=2,
                    border_radius=1,
                    bgcolor="#101010",
                )
                _levels.append(_c)
            self._spec_segments.append(_levels)
            _band_controls.append(
                ft.Column(_levels, spacing=1, tight=True, horizontal_alignment=ft.CrossAxisAlignment.CENTER)
            )

        self._spec_palette = _spec_palette
        self._spec_grid_content = ft.Row(_band_controls, spacing=2, vertical_alignment=ft.CrossAxisAlignment.END)
        self._spec_graphics_layer = ft.Stack([], expand=True)
        self._spec_graphics_host = ft.Container(
            expand=True,
            bgcolor="#05050c",
            content=self._spec_graphics_layer,
            padding=ft.padding.only(left=8, right=8, top=6, bottom=6),
        )
        self._spectrum_box = ft.Container(
            bgcolor="#060606",
            border=ft.border.all(1, "#2b2b2b"),
            border_radius=4,
            padding=ft.padding.only(left=6, right=6, top=4, bottom=0),
            width=self._spec_box_grid_size[0],
            height=self._spec_box_grid_size[1],
            content=self._spec_grid_content,
            tooltip="PC Audio Spectrum",
            ink=True,
            on_click=self._open_spectrum_source_selector,
        )
        
        # Spectrum audio source selector button
        self._spec_idle_settings_btn = ft.IconButton(
            icon=ft.Icons.TUNE,
            icon_size=12,
            icon_color="#ff9800",
            tooltip="Idle effects settings",
            style=ft.ButtonStyle(
                bgcolor="transparent",
                shape=ft.RoundedRectangleBorder(radius=6),
                padding=ft.padding.all(1),
            ),
            on_click=self._open_spectrum_idle_settings,
        )

        self._spec_settings_btn = ft.IconButton(
            icon=ft.Icons.MENU,
            icon_size=12,
            icon_color="#ff9800",
            tooltip="Spectrum settings",
            style=ft.ButtonStyle(
                bgcolor="transparent",
                shape=ft.RoundedRectangleBorder(radius=6),
                padding=ft.padding.all(1),
            ),
            on_click=self._open_spectrum_source_selector,
        )

        self._spec_sampling_btn = ft.IconButton(
            icon=ft.Icons.MIC,
            icon_size=12,
            tooltip="Sampling ON",
            style=ft.ButtonStyle(
                bgcolor="transparent",
                shape=ft.RoundedRectangleBorder(radius=5),
                padding=ft.padding.all(1),
            ),
            on_click=self._toggle_spec_sampling,
        )
        self._spec_idle_quick_btn = ft.IconButton(
            icon=ft.Icons.AUTO_AWESOME,
            icon_size=12,
            tooltip="Idle effects ON",
            style=ft.ButtonStyle(
                bgcolor="transparent",
                shape=ft.RoundedRectangleBorder(radius=5),
                padding=ft.padding.all(1),
            ),
            on_click=self._toggle_spec_idle_quick,
        )
        self._sync_spec_quick_buttons()

        self._title_combined_row = ft.Row([
            self._title_meta_row,
            self._title_anim_wrap,
        ], vertical_alignment="end", spacing=6)
        self._title_left_col = ft.Column([
            self._title_combined_row,
        ], spacing=0, tight=True, expand=True)
        self._title_left_wrap = ft.Container(
            content=self._title_left_col,
            padding=ft.padding.only(bottom=0),
            expand=True,
        )
        self._header_title_split = False

        self._header_right_row = ft.Row([
            ft.Row([
                self._border_speed_slider,
                _border_color_btn,
                _border_effect_btn,
            ], spacing=4, vertical_alignment=ft.CrossAxisAlignment.END),
            self.refresh_btn,
        ], spacing=10, vertical_alignment=ft.CrossAxisAlignment.END)

        self.header = ft.Row([
            self._title_left_wrap,
            ft.Row([
                ft.Column([self._spec_sampling_btn, self._spec_settings_btn], spacing=0, tight=True),
                self._spectrum_box,
                ft.Column([self._spec_idle_quick_btn, self._spec_idle_settings_btn], spacing=0, tight=True),
            ], spacing=2, vertical_alignment=ft.CrossAxisAlignment.END),
            self._header_right_row,
        ], alignment="start", vertical_alignment=ft.CrossAxisAlignment.END)

        self.top_update_row = ft.Row(
            [self.wledcc_update_btn],
            alignment="start",
            vertical_alignment=ft.CrossAxisAlignment.START,
        )
        
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
        _all_off  = ft.ElevatedButton("ALL OFF", on_click=lambda _: self.broadcast_power(False), bgcolor="red900", color="white", height=36)
        _all_on   = ft.ElevatedButton("ALL ON",  on_click=lambda _: self.broadcast_power(True),  bgcolor="green900", color="white", height=36)
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
        _ledfx_row_wide = ft.Row([
            self.ledfx_update_btn_wide,
            self.ledfx_ui_btn_wide,
            self.ledfx_btn_wide,
        ], spacing=6, vertical_alignment=ft.CrossAxisAlignment.END)
        _ledfx_row_narrow = ft.Row([
            self.ledfx_update_btn_narrow,
            self.ledfx_ui_btn_narrow,
            self.ledfx_btn_narrow,
        ], spacing=6, vertical_alignment=ft.CrossAxisAlignment.END)

        _bri_row_wide   = ft.Row([
            _slider_wide,
            self.scene_toggle_btn_wide,
            self.scene_row_wide,
        ], spacing=8, vertical_alignment=ft.CrossAxisAlignment.END)

        _bri_row_narrow = ft.Row([
            self.scene_toggle_btn_narrow,
            self.scene_row_narrow,
        ], spacing=8, vertical_alignment=ft.CrossAxisAlignment.END)

        # WIDE layout — single row, all controls side by side
        self._master_wide = ft.Row([
            ft.Column([
                ft.Row([_all_off, _all_on, _log_btn, _man_btn, _merge_btn], spacing=4)
            ], tight=True),
            ft.Column([
                _bri_row_wide,
            ], expand=True, horizontal_alignment="center"),
            ft.Column([_ledfx_row_wide],
                horizontal_alignment="end"),
        ], alignment="spaceBetween", visible=True, vertical_alignment=ft.CrossAxisAlignment.END)

        # NARROW layout — row 1: power+slider+ledfx, row 2: scenes only
        self._master_narrow = ft.Column([
            ft.Row([
                ft.Column([
                    ft.Row([_all_off, _all_on, _log_btn, _man_btn], spacing=4)
                ], tight=True),
                ft.Container(content=_slider_narrow, expand=True),
                ft.Column([_ledfx_row_narrow],
                    horizontal_alignment="end"),
            ], alignment="spaceBetween", vertical_alignment=ft.CrossAxisAlignment.END),
            ft.Row([
                self.scene_toggle_btn_narrow,
                self.scene_row_narrow,
            ], spacing=8, vertical_alignment=ft.CrossAxisAlignment.END),
        ], spacing=8, visible=False)

        self.master_bar = ft.Container(
            content=ft.Column([self._master_wide, self._master_narrow], spacing=0),
            padding=10, bgcolor="#121218", border_radius=10, border=ft.border.all(1, "#2b2b3b")
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
            [self.log_row, self.update_progress_row, self.top_update_row, self.header, self.master_bar,
             ft.Divider(height=10, color="transparent"), self._device_scroll],
            spacing=2,
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
        self._apply_header_layout(w)
        self._apply_master_layout(w)
        
        # Restore mixed card order (WLED + custom) exactly as saved.
        # Only force the + Add Device card to the end.
        _ordered_keys = [
            k for k in self.card_order
            if k != "__add_device__" and (k in self.cached_data or k in self.custom_devices)
        ]
        for k in _ordered_keys:
            if k in self.cached_data:
                self.add_device_card(self.cached_data[k], k, initial_online=False, dev_type=self.device_types.get(k, "wled"))
            elif k in self.custom_devices:
                info = self.custom_devices[k]
                self._add_custom_card(k, info["name"], info["url"], info.get("is_local", False), is_exe=info.get("is_exe", False))

        # Add any new/unordered WLED cards.
        for ip in [ip for ip in self.cached_data if ip not in _ordered_keys]:
            self.add_device_card(self.cached_data[ip], ip, initial_online=False, dev_type=self.device_types.get(ip, "wled"))

        # Add any new/unordered custom cards.
        for key, info in self.custom_devices.items():
            if key in _ordered_keys:
                continue
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
                    ft.Text("ADD", size=9, color="grey500", weight="bold"),
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
        """Fetch scenes from LedFx API. Retries up to 4 times if empty so LedFx has time to fully start."""
        max_attempts = 4
        for attempt in range(max_attempts):
            if attempt > 0:
                time.sleep(3)
            try:
                r = requests.get("http://localhost:8888/api/scenes", timeout=3).json()
                scenes_raw = r.get("scenes", {})
                names = {}
                scene_virtuals = {}
                if isinstance(scenes_raw, list):
                    for s in scenes_raw:
                        if not isinstance(s, dict):
                            continue
                        sid = s.get("id")
                        if not sid:
                            continue
                        names[sid] = s.get("name", sid)
                        vmap = {}
                        for v in (s.get("virtuals") or []):
                            if not isinstance(v, dict):
                                continue
                            vid = v.get("id")
                            if vid:
                                vmap[vid] = bool(v.get("active", False))
                        scene_virtuals[sid] = vmap
                elif isinstance(scenes_raw, dict):
                    for sid, s in scenes_raw.items():
                        if isinstance(s, dict):
                            names[sid] = s.get("name", sid)
                            vmap = {}
                            for v in (s.get("virtuals") or []):
                                if not isinstance(v, dict):
                                    continue
                                vid = v.get("id")
                                if vid:
                                    vmap[vid] = bool(v.get("active", False))
                            scene_virtuals[sid] = vmap
                        else:
                            # Some LedFx builds return scene values as simple names/strings.
                            names[sid] = str(s) if s is not None else sid
                            scene_virtuals[sid] = {}
                self.ledfx_scenes = names
                self.ledfx_scene_virtuals = scene_virtuals
                self.log(f"[LedFx] Fetched {len(names)} scene(s) from LedFx", color="grey500")
                # Only call restore once we have scenes, or on final attempt, to avoid premature give-up.
                if names or not self._pending_ledfx_scene_restore or attempt == max_attempts - 1:
                    break
                self.log(f"[LedFx] No scenes yet (attempt {attempt + 1}/{max_attempts}), retrying...", color="orange400")
            except Exception as e:
                self.log(f"[LedFx] Could not fetch scenes: {e}", color="orange400")
                if not self._pending_ledfx_scene_restore or attempt == max_attempts - 1:
                    break
                self.log(f"[LedFx] Retrying scene fetch ({attempt + 1}/{max_attempts})...", color="orange400")
        # Restore toggle button text and rebuild row regardless of success/failure
        if self._scene_mode == "ledfx":
            for _t in self._scene_toggle_btns:
                _t.text = "WLED SCENES"
                _t.bgcolor = "cyan"
                _t.color = "black"
                try: _t.update()
                except: pass
            self._rebuild_scene_rows_for_mode()
            self._schedule_ledfx_scene_restore_after_delay(delay=2.5)

    def toggle_scene_mode(self, e=None):
        """Toggle between WLED and LedFx scene sets."""
        if self._scene_mode == "wled":
            self._scene_mode = "ledfx"
            if self.auto_restore_ledfx_scene and self.last_ledfx_scene_id:
                self._pending_ledfx_scene_restore = True
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
        if self._scene_mode == "wled":
            threading.Thread(target=lambda: self._restore_last_wled_scene_after_delay(delay=2.5, source="wled-toggle"), daemon=True).start()

    def _rebuild_scene_rows_for_mode(self):
        """Rebuild scene rows based on current _scene_mode."""
        if self._scene_mode == "ledfx":
            self.ledfx_scene_btn_refs.clear()
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
        if self._scene_mode == "ledfx":
            self._apply_ledfx_scene_glow()
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
                self._activate_ledfx_scene(scene_id, scene_name=scene_name, remember=True, source="manual")
            threading.Thread(target=_send, daemon=True).start()

        btn = ft.Container(
            width=96, height=44,
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
        if scene_id not in self.ledfx_scene_btn_refs:
            self.ledfx_scene_btn_refs[scene_id] = []
        self.ledfx_scene_btn_refs[scene_id].append(btn)
        return btn

    def _apply_ledfx_scene_glow(self):
        """Update LedFx scene borders so the active scene glows like WLED scenes."""
        active = self.active_ledfx_scene_id
        glow_color = self.border_color if self.border_color else self._hue_to_hex(self.rainbow_hue)
        for scene_id, refs in list(self.ledfx_scene_btn_refs.items()):
            for ref in refs:
                try:
                    ref.border = ft.border.all(1, glow_color if active is not None and scene_id == active else "purple700")
                    ref.update()
                except:
                    pass

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
        """Convert hex to friendly name: exact match → hue dominance → nearest-neighbor."""
        if not isinstance(hex_color, str):
            return str(hex_color)

        h = hex_color.lower().strip()
        if h.startswith("#"):
            h = h[1:]
        if len(h) != 6:
            return hex_color

        try:
            r = int(h[0:2], 16)
            g = int(h[2:4], 16)
            b = int(h[4:6], 16)
        except ValueError:
            return hex_color

        h_norm = f"#{h}"
        names = {
            "#ff0000": "red",         "#ff1100": "red",
            "#00ff00": "green",       "#008000": "dark green",
            "#0000ff": "blue",        "#000080": "navy",
            "#ffff00": "yellow",      "#ffa500": "orange",
            "#ff8800": "orange",
            "#ff00ff": "magenta",     "#800080": "purple",
            "#00ffff": "cyan",        "#008080": "teal",
            "#ffffff": "white",       "#000000": "black",
            "#ff69b4": "pink",        "#ffc0cb": "pink",
            "#a52a2a": "brown",
            "#ff4500": "red-orange",
            "#7fff00": "chartreuse",
            "#4b0082": "indigo",      "#ee82ee": "violet",
            "#f5deb3": "wheat",       "#d2691e": "chocolate",
            "#40e0d0": "turquoise",   "#e0ffff": "light cyan",
            "#ffe4b5": "moccasin",    "#ffdead": "navajo white",
        }
        if h_norm in names:
            return names[h_norm]

        # Hue dominance detection: recognize dimmed/brightened versions by channel ratio.
        max_val = max(r, g, b)
        if max_val == 0:
            return "black"
        if max_val < 15:
            return "black"

        # Threshold for "dominant" (e.g., 75% rule: channel must be 75% of max)
        threshold = max_val * 0.75

        # Count dominant channels
        dom_r = r >= threshold
        dom_g = g >= threshold
        dom_b = b >= threshold

        # Pure single-channel dominance (red, green, blue)
        if dom_r and not dom_g and not dom_b:
            return "red"
        if dom_g and not dom_r and not dom_b:
            return "green"
        if dom_b and not dom_r and not dom_g:
            return "blue"

        # Two-channel dominance (yellow, magenta, cyan)
        if dom_r and dom_g and not dom_b:
            return "yellow"
        if dom_r and dom_b and not dom_g:
            return "magenta"
        if dom_g and dom_b and not dom_r:
            return "cyan"

        # All three dominant (near white/light)
        if dom_r and dom_g and dom_b:
            return "white" if max_val > 200 else "light gray"

        # High brightness, no clear dominance: nearest-neighbor
        if max_val > 150:
            palette = [
                ("orange", (255, 165, 0)),
                ("amber", (255, 191, 0)),
                ("chartreuse", (127, 255, 0)),
                ("lime", (0, 255, 0)),
                ("sky blue", (135, 206, 235)),
                ("indigo", (75, 0, 130)),
                ("violet", (238, 130, 238)),
                ("purple", (128, 0, 128)),
                ("pink", (255, 192, 203)),
                ("hot pink", (255, 105, 180)),
                ("peach", (255, 218, 185)),
                ("coral", (255, 127, 80)),
                ("red-orange", (255, 69, 0)),
                ("chocolate", (210, 105, 30)),
                ("tan", (210, 180, 140)),
                ("wheat", (245, 222, 179)),
                ("moccasin", (255, 228, 181)),
                ("navajo white", (255, 222, 173)),
            ]
        else:
            # Low brightness: dark/muted palette
            palette = [
                ("brown", (165, 42, 42)),
                ("gray", (128, 128, 128)),
                ("light gray", (211, 211, 211)),
            ]

        best_name = "color"
        best_dist = None
        for cname, (pr, pg, pb) in palette:
            dist = (r - pr) * (r - pr) + (g - pg) * (g - pg) + (b - pb) * (b - pb)
            if best_dist is None or dist < best_dist:
                best_dist = dist
                best_name = cname

        return best_name

    def _mh_label_for_ip(self, ip, fallback="MODE"):
        """Return the remembered button label for a MagicHome device."""
        mh = self.mh_mode.get(ip, {})
        pattern = mh.get("pattern") if isinstance(mh, dict) else None
        if pattern is not None:
            try:
                pattern = int(pattern)
                return MH_MODE_NAME_BY_PATTERN.get(pattern, f"EFFECT 0x{pattern:02X}")
            except Exception:
                return fallback

        rgb = self.mh_last_rgb.get(ip)
        if isinstance(rgb, (list, tuple)) and len(rgb) >= 3:
            try:
                return self._hex_to_name(f"#{int(rgb[0]):02x}{int(rgb[1]):02x}{int(rgb[2]):02x}")
            except Exception:
                return fallback

        return fallback

    def _apply_cached_mh_ui(self, ip):
        """Populate MH card controls from cached state without changing power state."""
        if self.device_types.get(ip) == "wled":
            return
        c = self.cards.get(ip)
        if not c:
            return

        bri = max(1, min(255, int(self.individual_brightness.get(ip, 128))))
        c["bri_slider"].value = bri

        mh = self.mh_mode.get(ip, {"pattern": None})
        if mh.get("pattern") is not None:
            spd_display = int((bri / 255) * 10) + 1
            c["bri_text"].value = f"SPD {spd_display}"
        else:
            c["bri_text"].value = f"{int((bri / 255) * 100)}%"

        label = self._mh_label_for_ip(ip)
        c["fx_label"].value = label.upper()
        c["preset_label"].value = label.upper()[:10] + ("…" if len(label) > 10 else "")

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
            autofocus=True, border_color="cyan", width=310,
            on_submit=lambda e: _probe(e),
        )
        status_text = ft.Text("", size=11, color="grey400")

        def _browse_exe(_):
            def _fill_path(path):
                field.value = path
                try: field.update()
                except: pass
            self._exe_pick_callback = _fill_path
            self.exe_picker.pick_files(
                dialog_title="Select EXE to launch",
                allowed_extensions=["exe"],
            )

        def _ensure_quick_custom_card(_key, _name, _url, _is_exe=False):
            _added = False
            _existing = self.custom_devices.get(_key)

            if not isinstance(_existing, dict):
                self.custom_devices[_key] = {
                    "name": _name,
                    "url": _url,
                    "is_local": False,
                    "is_exe": bool(_is_exe),
                    "auto_launch_start": False,
                    "auto_close_exit": False,
                }
                _added = True
            else:
                _existing.setdefault("name", _name)
                _existing.setdefault("url", _url)
                _existing["is_exe"] = bool(_is_exe)
                self.custom_devices[_key] = _existing

            self.custom_names[_key] = self.custom_devices[_key].get("name", _name)

            _meta = self._default_custom_cards_meta.setdefault(_key, {"auto_created": False, "user_deleted": False})
            _meta["auto_created"] = True
            _meta["user_deleted"] = False

            if _key not in self.cards:
                _info = self.custom_devices[_key]
                self._add_custom_card(
                    _key,
                    _info.get("name", _name),
                    _info.get("url", _url),
                    bool(_info.get("is_local", False)),
                    is_exe=bool(_info.get("is_exe", _is_exe)),
                )
                _added = True

            self._add_card_placeholder()
            self.save_cache()
            return _added

        def _quick_install_winamp(_):
            _ensure_quick_custom_card(DEFAULT_WINAMP_CARD_KEY, "WINAMP", "winamp.exe", _is_exe=True)
            dlg.open = False
            self.page.update()
            self.log("[Add] Winamp quick action selected", color="cyan")
            self._show_winamp_setup_dialog(DEFAULT_WINAMP_CARD_KEY)

        def _quick_add_spotify(_):
            _added = _ensure_quick_custom_card(DEFAULT_SPOTIFY_CARD_KEY, "SPOTIFY.COM", "https://open.spotify.com/", _is_exe=False)
            dlg.open = False
            self.page.update()
            if _added:
                self.log("[Add] Added 'SPOTIFY.COM' card", color="green400")
            else:
                self.log("[Add] 'SPOTIFY.COM' card already exists", color="orange400")

        def _quick_add_spotify_app(_):
            _key = "__default_spotify_app__"
            _ensure_quick_custom_card(_key, "SPOTIFY APP", "Spotify.exe", _is_exe=True)
            dlg.open = False
            self.page.update()
            self.log("[Add] Spotify app quick action selected", color="cyan")
            self._show_spotify_exe_setup_dialog(_key)

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
                    if os.path.basename(val).lower() == "winamp.exe":
                        status_text.value = "Winamp path not found. Opening Winamp install/setup options..."
                        status_text.color = "orange400"
                        try: status_text.update()
                        except: pass
                        _quick_install_winamp(None)
                        return
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
                self.custom_devices[key] = {
                    "name": name,
                    "url": url,
                    "is_local": is_local,
                    "is_exe": is_exe,
                    "auto_launch_start": False,
                    "auto_close_exit": False,
                }
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
                ft.Text("Enter an IP address, local hostname, web URL, or browse to an EXE:", size=12, color="grey400"),
                ft.Row([
                    field,
                    ft.ElevatedButton(
                        "Browse EXE",
                        icon=ft.Icons.FOLDER_OPEN,
                        bgcolor="#1e1e2e",
                        color="cyan",
                        on_click=_browse_exe,
                        style=ft.ButtonStyle(side=ft.BorderSide(1, "cyan")),
                    ),
                ], spacing=8, vertical_alignment=ft.CrossAxisAlignment.CENTER),
                ft.Row([
                    ft.ElevatedButton(
                        "Add Winamp",
                        icon=ft.Icons.LIBRARY_MUSIC,
                        bgcolor="#1e1e2e",
                        color="cyan",
                        on_click=_quick_install_winamp,
                        style=ft.ButtonStyle(side=ft.BorderSide(1, "cyan")),
                    ),
                    ft.ElevatedButton(
                        "Spotify.com",
                        icon=ft.Icons.LANGUAGE,
                        bgcolor="#1e1e2e",
                        color="cyan",
                        on_click=_quick_add_spotify,
                        style=ft.ButtonStyle(side=ft.BorderSide(1, "cyan")),
                    ),
                    ft.ElevatedButton(
                        "Spotify App",
                        icon=ft.Icons.ALBUM,
                        bgcolor="#1e1e2e",
                        color="cyan",
                        on_click=_quick_add_spotify_app,
                        style=ft.ButtonStyle(side=ft.BorderSide(1, "cyan")),
                    ),
                ], spacing=8),
                status_text,
            ], tight=True, spacing=10, width=480),
            actions=[
                ft.ElevatedButton("Probe", bgcolor="cyan", color="black", on_click=_probe),
                ft.TextButton("Cancel", on_click=_cancel),
            ]
        )
        self.page.overlay.append(dlg)
        dlg.open = True
        self.page.update()

    def _normalize_path(self, path):
        try:
            return os.path.normcase(os.path.normpath(path or ""))
        except:
            return (path or "").lower()

    def _find_running_exe_pid(self, exe_path):
        target = self._normalize_path(exe_path)
        if not target:
            return None
        _is_spotify_exe = False
        try:
            _is_spotify_exe = os.path.basename(target).lower() == "spotify.exe"
        except Exception:
            _is_spotify_exe = False
        for proc in psutil.process_iter(["pid", "exe", "cmdline"]):
            try:
                pexe = proc.info.get("exe")
                if pexe and self._normalize_path(pexe) == target:
                    return proc.info.get("pid")
                cmd = proc.info.get("cmdline") or []
                if cmd and self._normalize_path(cmd[0]) == target:
                    return proc.info.get("pid")
                if _is_spotify_exe:
                    _name = ""
                    try:
                        _name = (proc.name() or "").lower()
                    except Exception:
                        _name = ""
                    if _name == "spotify.exe":
                        return proc.info.get("pid")
            except:
                continue
        return None

    def _find_browser_binary(self):
        # Prefer Chrome; fall back to Edge.
        candidates = [
            ("chrome", os.path.join(os.environ.get("PROGRAMFILES", ""), "Google", "Chrome", "Application", "chrome.exe")),
            ("chrome", os.path.join(os.environ.get("PROGRAMFILES(X86)", ""), "Google", "Chrome", "Application", "chrome.exe")),
            ("chrome", os.path.join(os.environ.get("LOCALAPPDATA", ""), "Google", "Chrome", "Application", "chrome.exe")),
            ("edge", os.path.join(os.environ.get("PROGRAMFILES", ""), "Microsoft", "Edge", "Application", "msedge.exe")),
            ("edge", os.path.join(os.environ.get("PROGRAMFILES(X86)", ""), "Microsoft", "Edge", "Application", "msedge.exe")),
            ("edge", os.path.join(os.environ.get("LOCALAPPDATA", ""), "Microsoft", "Edge", "Application", "msedge.exe")),
        ]
        for browser, path in candidates:
            if path and os.path.exists(path):
                return browser, path
        chrome = shutil.which("chrome") or shutil.which("chrome.exe")
        if chrome:
            return "chrome", chrome
        edge = shutil.which("msedge") or shutil.which("msedge.exe")
        if edge:
            return "edge", edge
        return None, None

    def _find_running_url_pid(self, key, url):
        # URL cards use normal browser mode (no managed profile / PID tracking).
        # For Spotify web cards, treat as running only while web UI is open.
        # Desktop-app playback should not mark spotify.com card as active.
        try:
            if self._is_spotify_url_target(url):
                _web_open = self._is_spotify_web_window_open_now()
                return 1 if _web_open else None
        except Exception:
            return None
        return None

    def _set_custom_card_active(self, key, active):
        c = self.cards.get(key)
        if not c:
            return
        c["_is_active"] = bool(active)
        c["_glow_state"] = "on" if active else "offline"
        if not active:
            c["glow"].border = ft.border.all(2, "#2b2b3b")
            c["glow"].bgcolor = "#121420"

    def _is_winamp_target(self, path):
        try:
            return os.path.basename(path or "").lower() == "winamp.exe"
        except:
            return False

    def _default_custom_info_value(self, key):
        c = self.cards.get(key, {})
        target = c.get("_url") or self.custom_devices.get(key, {}).get("url", "")
        if self._is_winamp_target(target) or self._is_spotify_url_target(target) or self._is_spotify_exe_target(target):
            return "Now Playing: --"
        return target or ""

    def _set_custom_card_media_text(self, key, track_text=None):
        try:
            if threading.current_thread() is not threading.main_thread():
                self.page.call_from_thread(lambda: self._set_custom_card_media_text(key, track_text))
                return
        except Exception:
            pass

        c = self.cards.get(key)
        if not c:
            return
        info_text = c.get("info_text")
        if info_text is None:
            return

        _track = (track_text or "").strip()
        _value = f"Now Playing: {_track}" if _track else self._default_custom_info_value(key)
        if info_text.value == _value:
            return
        info_text.value = _value
        try:
            info_text.update()
        except Exception:
            pass

    def _get_winamp_now_playing_text(self):
        try:
            hwnd = win32gui.FindWindow("Winamp v1.x", None)
            if not hwnd:
                return None
            _title = (win32gui.GetWindowText(hwnd) or "").strip()
            if not _title:
                return None
            if _title.lower().endswith(" - winamp"):
                _title = _title[:-9].strip()
            if _title.lower() == "winamp":
                return None
            return _title or None
        except Exception:
            return None

    def _queue_winamp_play(self, path):
        if not self._is_winamp_target(path):
            return
        def _worker():
            # Winamp command IDs:
            # 40045 = Play, 40048 = Next track.
            for _ in range(20):
                if not self.running:
                    return
                try:
                    hwnd = win32gui.FindWindow("Winamp v1.x", None)
                    if hwnd:
                        win32gui.SendMessage(hwnd, win32con.WM_COMMAND, 40048, 0)
                        self.log("[App] Sent PLAY + NEXT to Winamp", color="cyan")
                        time.sleep(0.08)
                        win32gui.SendMessage(hwnd, win32con.WM_COMMAND, 40045, 0)
                        # Nudge once to avoid occasional first-track stickiness;
                        # Winamp's own random mode picks the song after this.
                        """  win32gui.SendMessage(hwnd, win32con.WM_COMMAND, 40045, 0)
                        # Nudge once to avoid occasional first-track stickiness;
                        # Winamp's own random mode picks the song after this.
                        time.sleep(0.08)
                        win32gui.SendMessage(hwnd, win32con.WM_COMMAND, 40048, 0)
                        self.log("[App] Sent PLAY + NEXT to Winamp", color="cyan") """
                        return
                except:
                    pass
                time.sleep(0.4)
        threading.Thread(target=_worker, daemon=True).start()

    def _send_winamp_command(self, key, command_id, action_label):
        """Send a direct Winamp WM_COMMAND action from card transport controls."""
        c = self.cards.get(key, {})
        target = c.get("_url") or self.custom_devices.get(key, {}).get("url")
        if not self._is_winamp_target(target):
            return

        name = c.get("name_label").value if c.get("name_label") else key
        try:
            hwnd = win32gui.FindWindow("Winamp v1.x", None)
            if not hwnd:
                self.log(f"[Winamp] '{name}' not running", color="grey500")
                return
            win32gui.SendMessage(hwnd, win32con.WM_COMMAND, int(command_id), 0)
            self.log(f"[Winamp] {action_label} — '{name}'", color="cyan")
        except Exception as ex:
            self.log(f"[Winamp] {action_label} failed for '{name}': {ex}", color="red400")

    def _focus_winamp_window(self):
        """Best-effort focus of the main Winamp window."""
        try:
            hwnd = win32gui.FindWindow("Winamp v1.x", None)
            if not hwnd:
                return False
            if win32gui.IsIconic(hwnd):
                win32gui.ShowWindow(hwnd, win32con.SW_RESTORE)
            else:
                win32gui.ShowWindow(hwnd, win32con.SW_SHOW)
            win32gui.SetWindowPos(
                hwnd, win32con.HWND_TOPMOST, 0, 0, 0, 0,
                win32con.SWP_NOMOVE | win32con.SWP_NOSIZE
            )
            win32gui.SetWindowPos(
                hwnd, win32con.HWND_NOTOPMOST, 0, 0, 0, 0,
                win32con.SWP_NOMOVE | win32con.SWP_NOSIZE
            )
            win32gui.BringWindowToTop(hwnd)
            win32gui.SetForegroundWindow(hwnd)
            return True
        except Exception:
            return False

    def _show_winamp_ui(self, key):
        """Bring Winamp to the foreground for manual interaction."""
        c = self.cards.get(key, {})
        target = c.get("_url") or self.custom_devices.get(key, {}).get("url")
        if not self._is_winamp_target(target):
            return
        _name = c.get("name_label").value if c.get("name_label") else key

        if self._focus_winamp_window():
            self.log(f"[Winamp] UI shown for '{_name}'", color="cyan")
            return

        self._launch_custom_target(key, auto=False)
        _end = time.monotonic() + 4.0
        _seen_window = False
        while self.running and (time.monotonic() < _end):
            try:
                _seen_window = bool(win32gui.FindWindow("Winamp v1.x", None))
            except Exception:
                _seen_window = False
            if _seen_window:
                break
            time.sleep(0.2)

        if _seen_window and self._focus_winamp_window():
            self.log(f"[Winamp] UI shown for '{_name}'", color="cyan")
            return

        self.log(f"[Winamp] Could not focus UI for '{_name}'", color="orange400")

    def _is_spotify_exe_target(self, path):
        """Return True if path points to the Spotify desktop app executable."""
        try:
            return os.path.basename((path or "").strip()).lower() == "spotify.exe"
        except Exception:
            return False

    def _get_spotify_desktop_hwnd(self):
        """Find the main Spotify desktop window handle via process scan."""
        try:
            _spotify_pids = set()
            for _proc in psutil.process_iter(["pid", "name"]):
                if (_proc.info.get("name") or "").lower() == "spotify.exe":
                    _spotify_pids.add(_proc.info["pid"])
            if not _spotify_pids:
                return None
            _found = []
            def _enum(hwnd, _):
                try:
                    if not win32gui.IsWindowVisible(hwnd):
                        return True
                    _title = (win32gui.GetWindowText(hwnd) or "").strip()
                    if not _title:
                        return True
                    _pid_out = ctypes.c_ulong(0)
                    ctypes.windll.user32.GetWindowThreadProcessId(hwnd, ctypes.byref(_pid_out))
                    if _pid_out.value in _spotify_pids:
                        _found.append(hwnd)
                except Exception:
                    pass
                return True
            win32gui.EnumWindows(_enum, None)
            if not _found:
                return None
            # Prefer the largest window (main player window)
            def _area(h):
                try:
                    r = win32gui.GetWindowRect(h)
                    return (r[2] - r[0]) * (r[3] - r[1])
                except Exception:
                    return 0
            return max(_found, key=_area)
        except Exception:
            return None

    def _focus_spotify_desktop_window(self):
        """Best-effort focus of the Spotify desktop app window."""
        try:
            hwnd = self._get_spotify_desktop_hwnd()
            if not hwnd:
                return False
            if win32gui.IsIconic(hwnd):
                win32gui.ShowWindow(hwnd, win32con.SW_RESTORE)
            else:
                win32gui.ShowWindow(hwnd, win32con.SW_SHOW)
            win32gui.SetWindowPos(
                hwnd, win32con.HWND_TOPMOST, 0, 0, 0, 0,
                win32con.SWP_NOMOVE | win32con.SWP_NOSIZE
            )
            win32gui.SetWindowPos(
                hwnd, win32con.HWND_NOTOPMOST, 0, 0, 0, 0,
                win32con.SWP_NOMOVE | win32con.SWP_NOSIZE
            )
            win32gui.BringWindowToTop(hwnd)
            win32gui.SetForegroundWindow(hwnd)
            return True
        except Exception:
            return False

    def _show_spotify_desktop_ui(self, key):
        """Bring Spotify desktop app to the foreground."""
        c = self.cards.get(key, {})
        target = c.get("_url") or self.custom_devices.get(key, {}).get("url")
        if not self._is_spotify_exe_target(target):
            return
        _name = c.get("name_label").value if c.get("name_label") else key

        if self._focus_spotify_desktop_window():
            self.log(f"[Spotify] Desktop UI shown for '{_name}'", color="cyan")
            return

        # Not running yet — launch then focus once the window appears
        self._launch_custom_target(key, auto=False)
        _end = time.monotonic() + 4.0
        _seen = False
        while self.running and (time.monotonic() < _end):
            try:
                _seen = self._get_spotify_desktop_hwnd() is not None
            except Exception:
                _seen = False
            if _seen:
                break
            time.sleep(0.2)

        if _seen and self._focus_spotify_desktop_window():
            self.log(f"[Spotify] Desktop UI shown for '{_name}'", color="cyan")
        else:
            self.log(f"[Spotify] Could not focus desktop UI for '{_name}'", color="orange400")

    def _send_spotify_desktop_command(self, key, action, log_action=True):
        """Send a global media key command for the Spotify desktop app."""
        c = self.cards.get(key, {})
        target = c.get("_url") or self.custom_devices.get(key, {}).get("url")
        if not self._is_spotify_exe_target(target):
            return
        name = c.get("name_label").value if c.get("name_label") else key
        _vk_map = {
            "PREV":       0xB1,  # VK_MEDIA_PREV_TRACK
            "PLAY_PAUSE": 0xB3,  # VK_MEDIA_PLAY_PAUSE
            "NEXT":       0xB0,  # VK_MEDIA_NEXT_TRACK
        }
        _vk = _vk_map.get(action.upper())
        if _vk is None:
            return
        try:
            ctypes.windll.user32.keybd_event(_vk, 0, 0, 0)
            ctypes.windll.user32.keybd_event(_vk, 0, 0x0002, 0)
            if log_action:
                self.log(f"[Spotify] {action.replace('_', '/')} — '{name}'", color="cyan")
        except Exception as ex:
            self.log(f"[Spotify] {action} failed for '{name}': {ex}", color="red400")

    def _queue_spotify_desktop_play(self, key):
        """After launching Spotify desktop, attempt a single autoplay trigger."""
        def _worker():
            _name = self.cards.get(key, {}).get("name_label")
            _name_val = _name.value if _name else key

            # Wait for desktop window to appear first.
            _end = time.monotonic() + 8.0
            _seen = False
            while self.running and (time.monotonic() < _end):
                try:
                    _seen = self._get_spotify_desktop_hwnd() is not None
                except Exception:
                    _seen = False
                if _seen:
                    break
                time.sleep(0.25)

            if not _seen:
                self.log(f"[Spotify] Autoplay skipped (window not ready) — '{_name_val}'", color="orange400")
                return

            if not self.running:
                return
            if bool(self._spotify_media_last_state):
                self.log(f"[Spotify] Autoplay confirmed — '{_name_val}'", color="grey500")
                return

            # Gentle focus assist once, then one play/pause trigger.
            try:
                self._focus_spotify_desktop_window()
            except Exception:
                pass
            time.sleep(0.12)

            self._send_spotify_desktop_command(key, "PLAY_PAUSE", log_action=False)

            _probe_end = time.monotonic() + 2.0
            while self.running and (time.monotonic() < _probe_end):
                if bool(self._spotify_media_last_state):
                    self.log(f"[Spotify] Autoplay started — '{_name_val}'", color="grey500")
                    return
                time.sleep(0.2)

            self.log(f"[Spotify] Autoplay pending manual play — '{_name_val}'", color="orange400")
        threading.Thread(target=_worker, daemon=True).start()

    def _get_spotify_desktop_now_playing_text(self):
        """Best-effort now-playing text from Spotify desktop window title."""
        try:
            hwnd = self._get_spotify_desktop_hwnd()
            if not hwnd:
                return None
            _title = (win32gui.GetWindowText(hwnd) or "").strip()
            if not _title:
                return None
            _low = _title.lower()
            if _low in ("spotify", "spotify free", "spotify premium"):
                return None
            if _low.endswith(" - spotify"):
                _title = _title[:-10].strip()
            _low2 = _title.lower()
            if _low2 in ("spotify", "spotify free", "spotify premium"):
                return None
            return _title or None
        except Exception:
            return None

    def _is_spotify_url_target(self, url):
        try:
            _u = (url or "").strip().lower()
            return ("spotify.com" in _u) or ("open.spotify.com" in _u)
        except Exception:
            return False

    def _is_spotify_gsmtc_session(self, session):
        try:
            _src = (getattr(session, "source_app_user_model_id", None) or "").lower()
            return "spotify" in _src
        except Exception:
            return False

    def _resolve_winrt_async_result(self, async_obj):
        """Resolve WinRT async results across winsdk/winrt variants."""
        if async_obj is None:
            return None
        try:
            if hasattr(async_obj, "__await__"):
                import asyncio
                return asyncio.run(async_obj)
        except Exception:
            pass
        try:
            _get = getattr(async_obj, "get", None)
            if callable(_get):
                return _get()
        except Exception:
            pass
        try:
            _result = getattr(async_obj, "result", None)
            if callable(_result):
                return _result()
        except Exception:
            pass
        return None

    def _get_spotify_window_track_text(self):
        """Best-effort track title from Spotify web browser window title."""
        import re as _re

        def _clean_spotify_title(_raw):
            _t = (_raw or "").strip()
            if not _t:
                return ""
            _t = _t.replace("•", " - ")
            # Collapse repeated separators and trim browser/site suffixes.
            _t = _re.sub(r"\s+", " ", _t)
            _suffix = (
                r"(?:open\.spotify\.com|spotify(?:\s*-\s*web\s*player)?|web\s*player|"
                r"google\s*chrome|chrome|microsoft\s*edge|edge|mozilla\s*firefox|firefox|"
                r"brave|opera|vivaldi|arc|browser)"
            )
            while True:
                _next = _re.sub(rf"\s*[-|:]\s*{_suffix}\s*$", "", _t, flags=_re.IGNORECASE).strip(" -|:")
                if _next == _t:
                    break
                _t = _next

            # If domain marker appears mid-title, keep left side.
            _low = _t.lower()
            _idx = _low.find("open.spotify.com")
            if _idx > 0:
                _t = _t[:_idx].strip(" -|:")

            _ban = {"spotify", "open.spotify.com", "spotify web player", "web player", "spotify - web player"}
            if _t.lower() in _ban:
                return ""
            return _t

        try:
            for _hwnd in self._find_spotify_track_windows():
                _title = (win32gui.GetWindowText(_hwnd) or "").strip()
                if not _title:
                    continue
                _low = _title.lower()
                if "spotify - web player" in _low and (" - " not in _title):
                    continue
                _clean = _clean_spotify_title(_title)
                if _clean and ("spotify" not in _clean.lower()) and ("open.spotify.com" not in _clean.lower()):
                    return _clean
                # Common browser title forms:
                # "Artist - Track - Spotify"
                # "Track - Spotify - Web Player"
                if " - spotify" in _low:
                    _idx = _low.rfind(" - spotify")
                    _track = _clean_spotify_title(_title[:_idx])
                    if _track:
                        return _track
                if _low.endswith(" - spotify"):
                    _track = _clean_spotify_title(_title[:-10])
                    if _track:
                        return _track
                if "spotify" in _low and " - " in _title:
                    _parts = [p.strip() for p in _title.split(" - ") if p.strip()]
                    if len(_parts) >= 2:
                        _track = _clean_spotify_title(" - ".join(_parts[:-1]))
                        if _track:
                            return _track
            # Fallback: PowerShell UI Automation reads non-focused Chrome tabs too.
            for _pst in self._scan_all_chrome_tabs_via_ps():
                _pst_low = _pst.lower()
                if "spotify" not in _pst_low and " \u2022 " not in _pst:
                    continue
                if " \u2022 " in _pst:
                    # Bullet format: "Track • Artist [extension junk...]"
                    # Take track (left of bullet) and artist (left of first " - " after bullet).
                    _bp = _pst.split(" \u2022 ", 1)
                    _bt = _bp[0].strip()
                    _ba = (_bp[1].split(" - ")[0].strip()) if len(_bp) > 1 else ""
                    _clean = (f"{_ba} - {_bt}" if _ba else _bt) or ""
                else:
                    _clean = _clean_spotify_title(_pst)
                if _clean and "spotify" not in _clean.lower() and "open.spotify.com" not in _clean.lower():
                    self._spotify_window_seen_until = max(
                        float(getattr(self, "_spotify_window_seen_until", 0.0)),
                        time.monotonic() + 45.0,
                    )
                    return _clean
            return None
        except Exception:
            return None

    def _find_spotify_track_windows(self):
        """Looser Spotify title scan for track text (does not drive close-tab actions)."""
        _targets = []
        _titles = []
        _has_spotify_card = self._has_spotify_card()
        _browser_proc_names = {
            "chrome.exe", "msedge.exe", "firefox.exe", "brave.exe",
            "opera.exe", "opera_gx.exe", "vivaldi.exe", "arc.exe",
            "iexplore.exe",
        }

        def _enum(hwnd, _):
            try:
                if not win32gui.IsWindowVisible(hwnd):
                    return True
                _title = (win32gui.GetWindowText(hwnd) or "").strip().lower()
                if not _title:
                    return True
                _cls = (win32gui.GetClassName(hwnd) or "").strip().lower()
                _proc_name = ""
                try:
                    _pid_out = ctypes.c_ulong(0)
                    ctypes.windll.user32.GetWindowThreadProcessId(hwnd, ctypes.byref(_pid_out))
                    if int(_pid_out.value) > 0:
                        _proc_name = (psutil.Process(int(_pid_out.value)).name() or "").lower()
                except Exception:
                    _proc_name = ""
                _bullet_music_hint = (" • " in _title)
                _spotify_hit = ("spotify" in _title) or ("open.spotify.com" in _title) or (_has_spotify_card and _bullet_music_hint)
                _browser_hint = any(b in _title for b in ["chrome", "edge", "firefox", "brave", "opera", "vivaldi", "arc", "browser", "web player"])
                _class_hint = _cls in (
                    "chrome_widgetwin_0",
                    "chrome_widgetwin_1",
                    "chrome_widgetwin_2",
                    "chrome_widgetwin_3",
                    "mozillawindowclass",
                    "applicationframewindow",
                    "windows.ui.core.corewindow",
                )
                _is_browser_proc = bool(_proc_name and (_proc_name in _browser_proc_names))
                if _spotify_hit and _is_browser_proc and (_browser_hint or _class_hint or (" - spotify" in _title) or ("| spotify" in _title)):
                    _targets.append(hwnd)
                    _titles.append(_title)
                    self._spotify_window_seen_until = max(float(getattr(self, "_spotify_window_seen_until", 0.0)), time.monotonic() + 45.0)
            except Exception:
                pass
            return True

        try:
            win32gui.EnumWindows(_enum, None)
        except Exception:
            return []
        self._log_spotify_window_titles("loose", _titles)
        return _targets

    def _scan_all_chrome_tabs_via_ps(self):
        """
        Use PowerShell + .NET UIAutomation to read ALL Chrome/Edge tab titles,
        including tabs that are not currently focused.  Results cached ~4 s.
        Returns list of title strings, empty on failure or if no Spotify card.
        """
        if not self._has_spotify_card():
            return []
        _now = time.monotonic()
        _cache = getattr(self, "_chrome_tab_cache", None)
        _cache_ts = float(getattr(self, "_chrome_tab_cache_ts", 0.0))
        if _cache is not None and (_now - _cache_ts) < 4.0:
            return list(_cache)
        try:
            # Single-line PS script: load UIAutomation, find browser top-level windows
            # by common classes, enumerate their TabItem descendants, print each name.
            _ps = (
                "Add-Type -AssemblyName UIAutomationClient;"
                "Add-Type -AssemblyName UIAutomationTypes;"
                "try{"
                "$r=[System.Windows.Automation.AutomationElement]::RootElement;"
                "$p0=[System.Windows.Automation.PropertyCondition]::new([System.Windows.Automation.AutomationElement]::ClassNameProperty,'Chrome_WidgetWin_0');"
                "$p1=[System.Windows.Automation.PropertyCondition]::new([System.Windows.Automation.AutomationElement]::ClassNameProperty,'Chrome_WidgetWin_1');"
                "$p2=[System.Windows.Automation.PropertyCondition]::new([System.Windows.Automation.AutomationElement]::ClassNameProperty,'Chrome_WidgetWin_2');"
                "$p3=[System.Windows.Automation.PropertyCondition]::new([System.Windows.Automation.AutomationElement]::ClassNameProperty,'Chrome_WidgetWin_3');"
                "$pm=[System.Windows.Automation.PropertyCondition]::new([System.Windows.Automation.AutomationElement]::ClassNameProperty,'MozillaWindowClass');"
                "$pa=[System.Windows.Automation.PropertyCondition]::new([System.Windows.Automation.AutomationElement]::ClassNameProperty,'ApplicationFrameWindow');"
                "$wc=[System.Windows.Automation.OrCondition]::new($p0,$p1,$p2,$p3,$pm,$pa);"
                "$ws=$r.FindAll([System.Windows.Automation.TreeScope]::Children,$wc);"
                "$tc=[System.Windows.Automation.PropertyCondition]::new("
                "[System.Windows.Automation.AutomationElement]::ControlTypeProperty,"
                "[System.Windows.Automation.ControlType]::TabItem);"
                "foreach($w in $ws){"
                "$ts=$w.FindAll([System.Windows.Automation.TreeScope]::Descendants,$tc);"
                "foreach($t in $ts){if($t.Current.Name){$t.Current.Name}}}"
                "}catch{}"
            )
            _proc = subprocess.run(
                ["powershell", "-NoProfile", "-NonInteractive", "-Command", _ps],
                capture_output=True,
                text=True,
                timeout=5.0,
                creationflags=win32con.CREATE_NO_WINDOW,
            )
            _titles = [_l.strip() for _l in (_proc.stdout or "").splitlines() if _l.strip()]
            self._chrome_tab_cache = _titles
            self._chrome_tab_cache_ts = time.monotonic()
            self._log_spotify_window_titles("ps", _titles)
            return _titles
        except Exception:
            self._chrome_tab_cache = []
            self._chrome_tab_cache_ts = time.monotonic()
            return []

    def _log_spotify_window_titles(self, source, titles):
        """Debug-only log for Spotify-related window titles, only when changed."""
        if not bool(getattr(self, "debug_mode", False)):
            return
        try:
            _vals = []
            _seen = set()
            for _t in (titles or []):
                _s = str(_t or "").strip()
                if not _s or (_s in _seen):
                    continue
                _seen.add(_s)
                _vals.append(_s)
            _sig = " || ".join(_vals) if _vals else "<none>"
            _prev_sig = self._spotify_title_log_cache.get(source)
            if _sig == _prev_sig:
                return
            self._spotify_title_log_cache[source] = _sig
            self.log(f"[Spotify][TabScan:{source}] {_sig}", color="grey500")
        except Exception:
            pass

    def _apply_spotify_track_metadata(self, title, artist=""):
        _title = (title or "").strip()
        _artist = (artist or "").strip()
        _track = ""
        if _title and _artist:
            _track = f"{_artist} - {_title}"
        elif _title:
            _track = _title

        if _track == (self._spotify_media_last_track or ""):
            return
        self._spotify_media_last_track = _track

        for _key, _c in list(self.cards.items()):
            if not _c.get("_is_custom"):
                continue
            _url = _c.get("_url") or self.custom_devices.get(_key, {}).get("url", "")
            if self._is_spotify_url_target(_url) or self._is_spotify_exe_target(_url):
                self._set_custom_card_media_text(_key, _track)

        if _track:
            self.log(f"[Spotify] Track -> {_track}", color="grey500")

    def _has_spotify_card(self):
        try:
            for _key, _info in list(self.custom_devices.items()):
                _url = _info.get("url", "")
                if self._is_spotify_url_target(_url) or self._is_spotify_exe_target(_url):
                    return True
        except Exception:
            pass
        return False

    def _has_active_spotify_card(self):
        try:
            for _key, _c in list(self.cards.items()):
                if not _c.get("_is_custom"):
                    continue
                _url = _c.get("_url") or self.custom_devices.get(_key, {}).get("url", "")
                if (self._is_spotify_url_target(_url) or self._is_spotify_exe_target(_url)) and bool(_c.get("_is_active")):
                    return True
        except Exception:
            pass
        return False

    def _is_winamp_running(self):
        try:
            for _proc in psutil.process_iter(["name"]):
                _n = (_proc.info.get("name") or "").lower()
                if _n == "winamp.exe":
                    return True
        except Exception:
            pass
        return False

    def _is_sa_audio_detected(self):
        try:
            _age = time.monotonic() - float(self._spec_last_audio_ts)
            return (not bool(self._spec_idle_active)) and (_age <= 2.0)
        except Exception:
            return False

    def _should_run_spotify_media_listener(self):
        if time.monotonic() < float(getattr(self, "_spotify_media_listener_earliest_ts", 0.0)):
            return False
        if (not self._has_spotify_card()) or self._is_winamp_running():
            return False

        _now = time.monotonic()
        if self._is_sa_audio_detected():
            self._spotify_listener_grace_until = max(float(getattr(self, "_spotify_listener_grace_until", 0.0)), _now + float(self._spotify_silence_grace_sec))
            return True

        if self._is_spotify_web_window_open() or self._has_active_spotify_card() or (self._spotify_media_last_state is True):
            self._spotify_listener_grace_until = max(float(getattr(self, "_spotify_listener_grace_until", 0.0)), _now + float(self._spotify_silence_grace_sec))
            return True

        return _now < float(getattr(self, "_spotify_listener_grace_until", 0.0))

    def _apply_spotify_playback_state(self, is_playing, source="GSMTC"):
        _playing = bool(is_playing)
        if _playing:
            self._spotify_listener_grace_until = max(float(getattr(self, "_spotify_listener_grace_until", 0.0)), time.monotonic() + float(self._spotify_silence_grace_sec))
        _updated = 0
        for _key, _c in list(self.cards.items()):
            if not _c.get("_is_custom"):
                continue
            _url = _c.get("_url") or self.custom_devices.get(_key, {}).get("url", "")
            if not self._is_spotify_url_target(_url):
                continue
            self._spotify_play_state[_key] = _playing
            self._update_custom_card_launch_ui(_key, _playing)
            _updated += 1
        if _updated > 0:
            self.log(f"[Spotify] {source} -> {'PLAYING' if _playing else 'PAUSED'}", color="grey500")

    def _update_spotify_media_listener_gate(self):
        _should = self._should_run_spotify_media_listener()
        _running = bool(self._spotify_media_listener_thread and self._spotify_media_listener_thread.is_alive())

        # Recover gracefully if thread died without passing through explicit gate-stop path.
        if self._spotify_media_listener_active and (not _running):
            self._spotify_media_listener_active = False
            self._spotify_media_listener_backend = None
            self._spotify_media_last_state = None
            self._apply_spotify_playback_state(False, source="GSMTC thread-exit")
            self.log("[Spotify] GSMTC listener stopped", color="grey500")

        if _should and (not self._spotify_media_listener_active):
            self._spotify_media_listener_stop.clear()
            self._spotify_media_listener_thread = threading.Thread(target=self._spotify_media_listener_loop, daemon=True)
            self._spotify_media_listener_active = True
            self._spotify_media_listener_thread.start()
            self.log("[Spotify] GSMTC listener started", color="grey500")
        elif (not _should) and self._spotify_media_listener_active:
            self._spotify_media_listener_stop.set()
            self._spotify_media_listener_active = False
            self._spotify_media_listener_backend = None
            self._spotify_media_last_state = None
            self._apply_spotify_track_metadata("", "")
            self._apply_spotify_playback_state(False, source="GSMTC gated-off")
            self.log("[Spotify] GSMTC listener stopped", color="grey500")

    def _spotify_media_listener_loop(self):
        """Best-effort GSMTC watcher for Spotify playback state (gated by app conditions)."""
        _manager = None
        _backend = None
        _startup_checked = False

        def _status_is_playing(_status):
            # GSMTC enum values (Windows): Playing=4, Paused=5, Stopped=3
            # Keep this tolerant across winsdk/runtime variants.
            try:
                if int(_status) == 4:
                    return True
            except Exception:
                pass
            _txt = str(_status).lower()
            if "playing" in _txt:
                return True
            _name = getattr(_status, "name", None)
            if isinstance(_name, str) and _name.lower() == "playing":
                return True
            return False

        while self.running and (not self._spotify_media_listener_stop.is_set()):
            if not self._should_run_spotify_media_listener():
                break

            if _manager is None:
                # Lazy init: only attempt WinRT APIs while gate is open.
                try:
                    import asyncio
                    import importlib
                    _mod_name = "winsdk" + ".windows.media.control"
                    _media_ctrl = importlib.import_module(_mod_name)
                    _GSMTCManager = getattr(_media_ctrl, "GlobalSystemMediaTransportControlsSessionManager", None)
                    if _GSMTCManager is None:
                        raise RuntimeError("GSMTC manager type not found")
                    _manager = asyncio.run(_GSMTCManager.request_async())
                    _backend = "winsdk"
                    self._spotify_media_listener_backend = _backend
                except Exception:
                    _manager = None
                    _backend = None
                    self._spotify_media_listener_backend = None
                    if not _startup_checked and self._spotify_listener_loaded_at_start is None:
                        self._spotify_listener_loaded_at_start = False
                        _startup_checked = True
                    # No compatible backend available in this environment.
                    time.sleep(2.0)
                    continue

            _playing = None
            _track_title = ""
            _track_artist = ""
            try:
                _session = _manager.get_current_session() if _manager else None
                _sessions = []
                try:
                    _sessions = list(_manager.get_sessions()) if _manager else []
                except Exception:
                    _sessions = []

                # Use current session first; if missing, scan available sessions.
                _candidates = []
                if _session is not None:
                    _candidates.append(_session)
                for _s in _sessions:
                    if _s is None or _s in _candidates:
                        continue
                    _candidates.append(_s)

                _spotify_candidates = [_s for _s in _candidates if self._is_spotify_gsmtc_session(_s)]
                _probe_candidates = _spotify_candidates if _spotify_candidates else _candidates

                if _probe_candidates:
                    _playing = False
                    for _s in _probe_candidates:
                        try:
                            _playback = _s.get_playback_info()
                            _status = getattr(_playback, "playback_status", None)
                            if _status_is_playing(_status):
                                _playing = True
                            if not _track_title:
                                try:
                                    _get_media = getattr(_s, "try_get_media_properties_async", None) or getattr(_s, "get_media_properties_async", None)
                                    if _get_media is not None:
                                        _props = self._resolve_winrt_async_result(_get_media())
                                        _track_title = (getattr(_props, "title", "") or "").strip()
                                        _track_artist = (getattr(_props, "artist", "") or "").strip()
                                except Exception:
                                    pass
                            if _playing and _track_title:
                                break
                        except Exception:
                            continue
                    if (not _startup_checked) and (self._spotify_listener_loaded_at_start is None):
                        self._spotify_listener_loaded_at_start = True
                        _startup_checked = True
                else:
                    _playing = False
                    if (not _startup_checked) and (self._spotify_listener_loaded_at_start is None):
                        self._spotify_listener_loaded_at_start = False
                        _startup_checked = True
            except Exception:
                # Force re-init on next pass.
                _manager = None
                _backend = None
                self._spotify_media_listener_backend = None
                time.sleep(1.0)
                continue

            if _playing is not None and _playing != self._spotify_media_last_state:
                self._spotify_media_last_state = _playing
                self._apply_spotify_playback_state(_playing, source="GSMTC")
            if not _track_title:
                _track_title = self._get_spotify_window_track_text() or ""
            self._apply_spotify_track_metadata(_track_title, _track_artist)

            time.sleep(1.0)

        self._spotify_media_listener_backend = None
        self._spotify_media_listener_active = False

    def _sync_spotify_card_glow(self, key):
        """Apply Spotify glow while Spotify web UI is open."""
        c = self.cards.get(key)
        if not c:
            return
        if not c.get("_is_custom"):
            return
        if not self._is_spotify_url_target(c.get("_url") or self.custom_devices.get(key, {}).get("url")):
            return

        _web_open = self._is_spotify_web_window_open_now()
        _engaged = bool(_web_open)
        c["_glow_state"] = "on" if _engaged else "off"
        if not _engaged:
            c["glow"].border = ft.border.all(2, "#2b2b3b")
            c["glow"].bgcolor = "#121420"
        try:
            c["glow"].update()
        except Exception:
            pass

    def _send_spotify_command(self, key, action, allow_open_if_missing=True):
        """Send global media-key commands for Spotify web cards (Windows)."""
        c = self.cards.get(key, {})
        target = c.get("_url") or self.custom_devices.get(key, {}).get("url")
        if not self._is_spotify_url_target(target):
            return

        name = c.get("name_label").value if c.get("name_label") else key
        _action = str(action).upper()
        self._spotify_keepalive_until[key] = time.monotonic() + 8.0
        _vk_map = {
            "PREV": 0xB1,        # VK_MEDIA_PREV_TRACK
            "PLAY_PAUSE": 0xB3,  # VK_MEDIA_PLAY_PAUSE
            "PLAY": 0xB3,
            "PAUSE": 0xB3,
            "NEXT": 0xB0,        # VK_MEDIA_NEXT_TRACK
        }
        _vk = _vk_map.get(_action)
        if _vk is None:
            return

        _is_playing = bool(self._spotify_play_state.get(key, False))

        # If user requests playback while Spotify web UI is not open,
        # open the web player first, then queue PLAY after load.
        if _action in ("PLAY", "PLAY_PAUSE"):
            _requests_play = (_action == "PLAY") or (_action == "PLAY_PAUSE" and (not _is_playing))
            if _requests_play and (not self._is_spotify_web_window_open()):
                if allow_open_if_missing:
                    self.log(f"[Spotify] Web UI not open — opening '{name}' before PLAY", color="grey500")
                    self._ensure_spotify_playback(key, target, auto=False, allow_open=True)
                else:
                    self.log(f"[Spotify] PLAY skipped (web UI not open) — '{name}'", color="grey500")
                return

        # Windows global media key has no true "pause-only" command.
        # Guard against accidental resume when already paused/stopped.
        if _action == "PAUSE" and not _is_playing:
            self.log(f"[Spotify] PAUSE skipped (already paused) — '{name}'", color="grey500")
            self._spotify_play_state[key] = False
            self._sync_spotify_card_glow(key)
            return

        try:
            # key down then key up
            ctypes.windll.user32.keybd_event(_vk, 0, 0, 0)
            ctypes.windll.user32.keybd_event(_vk, 0, 0x0002, 0)
            if _action == "PLAY":
                self._spotify_play_state[key] = True
            elif _action == "PAUSE":
                self._spotify_play_state[key] = False
            elif _action == "PLAY_PAUSE":
                self._spotify_play_state[key] = not _is_playing
            elif _action in ("NEXT", "PREV") and _is_playing:
                self._spotify_play_state[key] = True
            self._sync_spotify_card_glow(key)
            self.log(f"[Spotify] {_action.replace('_', '/')} — '{name}'", color="cyan")
        except Exception as ex:
            self.log(f"[Spotify] {action} failed for '{name}': {ex}", color="red400")

    def _queue_spotify_play(self, key):
        """After opening spotify.com, send a delayed PLAY media key."""
        def _worker():
            # Give browser tab enough time to load/register media session.
            time.sleep(4.0)
            if not self.running:
                return
            try:
                _ok = False
                # Some browser builds ignore first-play in background; retry a few times.
                for _attempt in range(3):
                    if not self.running:
                        return
                    self._focus_spotify_window(maximize=False)
                    time.sleep(0.25)
                    self._send_spotify_command(key, "PLAY", allow_open_if_missing=False)
                    time.sleep(0.6)
                    self._try_spotify_window_space()

                    _probe_end = time.monotonic() + 2.8
                    while self.running and (time.monotonic() < _probe_end):
                        # Confirm playback via GSMTC; fallback to SA audio activity.
                        # Ignore optimistic card state to avoid minimizing too early.
                        if (self._spotify_media_last_state is True) or self._is_sa_audio_detected():
                            _ok = True
                            break
                        time.sleep(0.25)

                    if _ok:
                        break
                    time.sleep(0.7 + (0.3 * _attempt))

                if _ok:
                    _hwnd = self._get_spotify_window_hwnd()
                    if _hwnd:
                        try:
                            win32gui.ShowWindow(_hwnd, win32con.SW_MINIMIZE)
                        except Exception:
                            pass
                else:
                    _name = self.cards.get(key, {}).get("name_label")
                    _name_val = _name.value if _name else key
                    self.log(f"[Spotify] Waiting for interaction in '{_name_val}' (autoplay policy)", color="orange400")
            except Exception:
                pass
        threading.Thread(target=_worker, daemon=True).start()

    def _get_spotify_window_hwnd(self):
        try:
            _targets = self._find_spotify_browser_windows() or self._find_spotify_track_windows()
            if not _targets:
                return None
            return _targets[0]
        except Exception:
            return None

    def _focus_spotify_window(self, maximize=False):
        """Best-effort focus of a Spotify browser window/tab host."""
        try:
            hwnd = self._get_spotify_window_hwnd()
            if not hwnd:
                return False
            try:
                if win32gui.IsIconic(hwnd):
                    win32gui.ShowWindow(hwnd, win32con.SW_RESTORE)
                elif maximize:
                    win32gui.ShowWindow(hwnd, win32con.SW_MAXIMIZE)
                win32gui.SetForegroundWindow(hwnd)
                return True
            except Exception:
                return False
        except Exception:
            return False

    def _resolve_windows_browser_exe(self, exe_name):
        """Resolve browser executable path on Windows (PATH, registry App Paths, common install paths)."""
        _exe = (exe_name or "").strip()
        if not _exe:
            return None
        try:
            _w = shutil.which(_exe)
            if _w:
                return _w
        except Exception:
            pass

        _app_exe = _exe if _exe.lower().endswith(".exe") else f"{_exe}.exe"

        if winreg is not None:
            _roots = []
            try:
                _roots.append(winreg.HKEY_CURRENT_USER)
                _roots.append(winreg.HKEY_LOCAL_MACHINE)
            except Exception:
                _roots = []
            for _root in _roots:
                try:
                    _kpath = rf"SOFTWARE\Microsoft\Windows\CurrentVersion\App Paths\{_app_exe}"
                    with winreg.OpenKey(_root, _kpath) as _k:
                        _p, _ = winreg.QueryValueEx(_k, None)
                        if _p and os.path.exists(_p):
                            return _p
                except Exception:
                    pass

        _pf = os.environ.get("ProgramFiles", r"C:\Program Files")
        _pf86 = os.environ.get("ProgramFiles(x86)", r"C:\Program Files (x86)")
        _la = os.environ.get("LOCALAPPDATA", "")
        _cand = {
            "chrome": [
                os.path.join(_pf, "Google", "Chrome", "Application", "chrome.exe"),
                os.path.join(_pf86, "Google", "Chrome", "Application", "chrome.exe"),
            ],
            "msedge": [
                os.path.join(_pf, "Microsoft", "Edge", "Application", "msedge.exe"),
                os.path.join(_pf86, "Microsoft", "Edge", "Application", "msedge.exe"),
            ],
            "brave": [
                os.path.join(_pf, "BraveSoftware", "Brave-Browser", "Application", "brave.exe"),
                os.path.join(_pf86, "BraveSoftware", "Brave-Browser", "Application", "brave.exe"),
            ],
            "firefox": [
                os.path.join(_pf, "Mozilla Firefox", "firefox.exe"),
                os.path.join(_pf86, "Mozilla Firefox", "firefox.exe"),
            ],
        }
        if _la:
            _cand.setdefault("chrome", []).append(os.path.join(_la, "Google", "Chrome", "Application", "chrome.exe"))
            _cand.setdefault("brave", []).append(os.path.join(_la, "BraveSoftware", "Brave-Browser", "Application", "brave.exe"))

        for _p in _cand.get(_exe.lower(), []):
            try:
                if _p and os.path.exists(_p):
                    return _p
            except Exception:
                pass
        return None

    def _launch_spotify_dedicated_window(self, target, minimize=True, allow_shared_fallback=False):
        """Open Spotify in its own browser window, then optionally minimize it."""
        _opened = False
        _candidates = [
            ("chrome", [f"--app={target}", "--new-window"]),
            ("msedge", [f"--app={target}", "--new-window"]),
            ("brave", [f"--app={target}", "--new-window"]),
            ("firefox", ["-new-window", target]),
        ]
        for _exe, _args in _candidates:
            _resolved = self._resolve_windows_browser_exe(_exe)
            try:
                if _resolved:
                    subprocess.Popen([_resolved] + _args)
                else:
                    # Let cmd.exe resolve aliases/app paths (works on some Windows setups)
                    subprocess.Popen(
                        ["cmd", "/c", "start", "", _exe] + _args,
                        creationflags=win32con.CREATE_NO_WINDOW,
                    )
                _opened = True
                break
            except Exception:
                continue

        if (not _opened) and allow_shared_fallback:
            try:
                self.page.launch_url(target)
                _opened = True
            except Exception:
                return False

        if not _opened:
            return False

        if minimize:
            _end = time.monotonic() + 6.0
            while self.running and (time.monotonic() < _end):
                hwnd = self._get_spotify_window_hwnd()
                if hwnd:
                    try:
                        win32gui.ShowWindow(hwnd, win32con.SW_MINIMIZE)
                    except Exception:
                        pass
                    break
                time.sleep(0.2)
        return True

    def _show_spotify_web_ui(self, key, maximize=True):
        """Bring Spotify web UI to foreground for manual interaction."""
        c = self.cards.get(key, {})
        target = c.get("_url") or self.custom_devices.get(key, {}).get("url")
        if not self._is_spotify_url_target(target):
            return
        _name = c.get("name_label").value if c.get("name_label") else key

        if not self._is_spotify_web_window_open_now():
            self._ensure_spotify_playback(key, target, auto=False, allow_open=True)
            time.sleep(0.5)

        if self._focus_spotify_window(maximize=maximize):
            self.log(f"[Spotify] Web UI shown for '{_name}'", color="cyan")
        else:
            self.log(f"[Spotify] Could not focus web UI for '{_name}'", color="orange400")

    def _try_spotify_window_space(self):
        """Best-effort SPACE key to a foreground Spotify browser window."""
        try:
            _focused = self._focus_spotify_window()
            if not _focused:
                return
            hwnd = win32gui.GetForegroundWindow()
            if not hwnd:
                return
            win32gui.PostMessage(hwnd, win32con.WM_KEYDOWN, win32con.VK_SPACE, 0)
            win32gui.PostMessage(hwnd, win32con.WM_KEYUP, win32con.VK_SPACE, 0)
        except Exception:
            pass

    def _find_spotify_browser_windows(self):
        """Return visible browser window handles likely associated with Spotify web UI."""
        _targets = []
        _titles = []
        _has_spotify_card = self._has_spotify_card()
        _browser_proc_names = {
            "chrome.exe", "msedge.exe", "firefox.exe", "brave.exe",
            "opera.exe", "opera_gx.exe", "vivaldi.exe", "arc.exe",
            "iexplore.exe",
        }

        def _enum(hwnd, _):
            try:
                _title = (win32gui.GetWindowText(hwnd) or "").strip().lower()
                if not _title:
                    return True
                _pid = None
                _proc_name = ""
                try:
                    _pid_out = ctypes.c_ulong(0)
                    ctypes.windll.user32.GetWindowThreadProcessId(hwnd, ctypes.byref(_pid_out))
                    _pid = int(_pid_out.value)
                    if _pid > 0:
                        _proc_name = (psutil.Process(_pid).name() or "").lower()
                except Exception:
                    _pid = None
                    _proc_name = ""
                # Title-based browser matching misses PWA/standalone windows.
                # Prefer class-based detection with title fallback.
                _browser_hit = self._is_known_browser_hwnd(hwnd) or any(
                    b in _title for b in ["chrome", "edge", "firefox", "brave", "opera", "vivaldi", "arc", "browser"]
                )
                # Prevent Spotify desktop windows (also Chromium class) from being
                # treated as browser tabs for spotify.com card state.
                if _browser_hit and _proc_name and (_proc_name not in _browser_proc_names):
                    _browser_hit = False
                _spotify_hit = ("spotify" in _title) or ("open.spotify.com" in _title) or (_has_spotify_card and (" • " in _title))
                if _browser_hit and _spotify_hit:
                    _targets.append(hwnd)
                    _titles.append(_title)
                    self._spotify_window_seen_until = max(float(getattr(self, "_spotify_window_seen_until", 0.0)), time.monotonic() + 45.0)
            except Exception:
                pass
            return True

        try:
            win32gui.EnumWindows(_enum, None)
        except Exception:
            return []
        self._log_spotify_window_titles("strict", _titles)
        return _targets

    def _is_known_browser_hwnd(self, hwnd):
        try:
            _cls = (win32gui.GetClassName(hwnd) or "").strip().lower()
            return _cls in (
                "chrome_widgetwin_0",
                "chrome_widgetwin_1",
                "mozillawindowclass",
                "applicationframewindow",
            )
        except Exception:
            return False

    def _is_spotify_web_window_open(self):
        try:
            if len(self._find_spotify_browser_windows()) > 0:
                return True
            if len(self._find_spotify_track_windows()) > 0:
                return True
            return time.monotonic() < float(getattr(self, "_spotify_window_seen_until", 0.0))
        except Exception:
            return False

    def _is_spotify_web_window_open_now(self):
        """Immediate Spotify web-window check (no recently-seen cache)."""
        try:
            if len(self._find_spotify_browser_windows()) > 0:
                return True
            if len(self._find_spotify_track_windows()) > 0:
                return True
        except Exception:
            pass
        return False

    def _close_spotify_browser_windows(self):
        """Best-effort close for detected Spotify tabs (Ctrl+W). Returns count sent."""
        _closed = 0
        for _hwnd in self._find_spotify_browser_windows():
            try:
                # Bring the Spotify tab window to foreground, then close only the active tab.
                # This avoids closing the whole browser window with unrelated tabs.
                if win32gui.IsIconic(_hwnd):
                    win32gui.ShowWindow(_hwnd, win32con.SW_RESTORE)
                win32gui.SetForegroundWindow(_hwnd)
                time.sleep(0.08)
                ctypes.windll.user32.keybd_event(win32con.VK_CONTROL, 0, 0, 0)
                ctypes.windll.user32.keybd_event(ord("W"), 0, 0, 0)
                ctypes.windll.user32.keybd_event(ord("W"), 0, 0x0002, 0)
                ctypes.windll.user32.keybd_event(win32con.VK_CONTROL, 0, 0x0002, 0)
                _closed += 1
            except Exception:
                continue
        return _closed

    def _close_foreground_browser_tab(self):
        """Fallback: close active tab in foreground browser window. Returns True if sent."""
        try:
            _hwnd = win32gui.GetForegroundWindow()
            if not _hwnd or (not self._is_known_browser_hwnd(_hwnd)):
                return False
            ctypes.windll.user32.keybd_event(win32con.VK_CONTROL, 0, 0, 0)
            ctypes.windll.user32.keybd_event(ord("W"), 0, 0, 0)
            ctypes.windll.user32.keybd_event(ord("W"), 0, 0x0002, 0)
            ctypes.windll.user32.keybd_event(win32con.VK_CONTROL, 0, 0x0002, 0)
            return True
        except Exception:
            return False

    def _spotify_is_active_now(self, key=None):
        try:
            if key is not None and bool(self._spotify_play_state.get(key, False)):
                return True
            if self._spotify_media_last_state is True:
                return True
        except Exception:
            pass
        return False

    def _ensure_spotify_playback(self, key, target, auto=False, allow_open=True, force_dedicated_open=False):
        """Ensure Spotify is playing: prefer existing listener/tab, fallback to opening a fresh tab."""
        _name = self.cards.get(key, {}).get("name_label")
        _name_val = _name.value if _name else key
        self._spotify_keepalive_until[key] = time.monotonic() + 20.0

        if force_dedicated_open and allow_open:
            _opened = self._launch_spotify_dedicated_window(target, minimize=False, allow_shared_fallback=False)
            if not _opened:
                self.log(f"[Web] Could not launch dedicated Spotify window for '{_name_val}'", color="red400")
                return False
            self.custom_launch_state.pop(key, None)
            self._spotify_play_state[key] = True  # Optimistic: GSMTC will correct if needed
            self._update_custom_card_launch_ui(key, True)
            self._queue_spotify_play(key)
            if not bool(getattr(self, "_spotify_window_tip_shown", False)):
                self._spotify_window_tip_shown = True
                self.log("[Spotify] Tip: Track metadata is most reliable when Spotify is in its own browser window.", color="grey500")
            _prefix = "[Auto Start]" if auto else "[Web]"
            self.log(f"{_prefix} Opened '{_name_val}' in dedicated browser window", color="green400")
            return True

        # If already active, don't spawn a duplicate tab.
        _web_open_now = self._is_spotify_web_window_open_now()
        if self._spotify_is_active_now(key) and _web_open_now:
            self._update_custom_card_launch_ui(key, True)
            self.log(f"[Spotify] Already active — skip opening '{_name_val}'", color="grey500")
            return True
        if self._spotify_is_active_now(key) and (not _web_open_now):
            # Stale active state (e.g., just closed) should not block re-open.
            self._spotify_play_state[key] = False
            self._spotify_media_last_state = False
            self._spotify_keepalive_until.pop(key, None)

        _web_open = self._is_spotify_web_window_open_now()
        if _web_open:
            self._update_custom_card_launch_ui(key, True)
            self._focus_spotify_window()
            self.log(f"[Spotify] Existing web UI found — sending PLAY for '{_name_val}'", color="grey500")
            self._send_spotify_command(key, "PLAY", allow_open_if_missing=False)
            _probe_end = time.monotonic() + 2.5
            while self.running and (time.monotonic() < _probe_end):
                self._update_spotify_media_listener_gate()
                if self._spotify_is_active_now(key):
                    return True
                time.sleep(0.2)

            # Stale/old tab path: if PLAY probe fails, open fresh tab when allowed.
            if not allow_open:
                self.log(f"[Spotify] PLAY probe failed (no open fallback) for '{_name_val}'", color="orange400")
                return False
            self.log(f"[Spotify] Existing tab did not attach to listener — opening fresh tab for '{_name_val}'", color="grey500")

        if not allow_open:
            return False

        # Open fresh tab and trigger play once page has had time to load.
        _opened = self._launch_spotify_dedicated_window(target, minimize=False, allow_shared_fallback=False)
        if not _opened:
            self.log(f"[Web] Could not launch dedicated Spotify window for '{_name_val}'", color="red400")
            return False
        self.custom_launch_state.pop(key, None)
        self._spotify_play_state[key] = True  # Optimistic: GSMTC will correct if needed
        self._update_custom_card_launch_ui(key, True)
        self._queue_spotify_play(key)
        if not bool(getattr(self, "_spotify_window_tip_shown", False)):
            self._spotify_window_tip_shown = True
            self.log("[Spotify] Tip: Track metadata is most reliable when Spotify is in its own browser window.", color="grey500")
        _prefix = "[Auto Start]" if auto else "[Web]"
        self.log(f"{_prefix} Opened '{_name_val}' in dedicated browser window", color="green400")
        return True

    def _update_custom_card_launch_ui(self, key, active):
        c = self.cards.get(key)
        if not c:
            return
        # Keep spotify.com card state synced to actual web UI visibility.
        _target_url = c.get("_url") or self.custom_devices.get(key, {}).get("url")
        if self._is_spotify_url_target(_target_url):
            active = self._is_spotify_web_window_open_now()

        btn_text = c.get("launch_btn_text")
        btn_icon = c.get("launch_btn_icon")
        btn = c.get("launch_btn")
        spotify_prev_btn = c.get("spotify_prev_btn")
        spotify_playpause_btn = c.get("spotify_playpause_btn")
        spotify_next_btn = c.get("spotify_next_btn")
        spotify_show_ui_btn = c.get("spotify_show_ui_btn")
        if btn_text is not None:
            btn_text.value = "CLOSE" if active else ("LAUNCH" if c.get("_is_exe") else "OPEN")
            btn_text.color = "#ffb4b4" if active else "white"
        if btn_icon is not None:
            btn_icon.name = ft.Icons.STOP if active else (ft.Icons.PLAY_ARROW if c.get("_is_exe") else ft.Icons.OPEN_IN_BROWSER)
            btn_icon.color = "#ffb4b4" if active else "white"
        if btn is not None:
            btn.bgcolor = "#4a1111" if active else "#1a1a2e"
        if self._is_spotify_url_target(_target_url):
            _disabled = not bool(active)
            if spotify_prev_btn is not None:
                spotify_prev_btn.disabled = _disabled
            if spotify_playpause_btn is not None:
                spotify_playpause_btn.disabled = _disabled
            if spotify_next_btn is not None:
                spotify_next_btn.disabled = _disabled
            if spotify_show_ui_btn is not None:
                spotify_show_ui_btn.disabled = _disabled
        self._set_custom_card_active(key, active)
        # Spotify URL cards glow only while Spotify web UI is open.
        if self._is_spotify_url_target(c.get("_url") or self.custom_devices.get(key, {}).get("url")):
            self._sync_spotify_card_glow(key)
        try:
            if btn_text is not None: btn_text.update()
        except:
            pass
        try:
            if btn_icon is not None: btn_icon.update()
        except:
            pass
        try:
            if btn is not None: btn.update()
        except:
            pass
        try:
            if spotify_prev_btn is not None: spotify_prev_btn.update()
        except:
            pass
        try:
            if spotify_playpause_btn is not None: spotify_playpause_btn.update()
        except:
            pass
        try:
            if spotify_next_btn is not None: spotify_next_btn.update()
        except:
            pass
        try:
            if spotify_show_ui_btn is not None: spotify_show_ui_btn.update()
        except:
            pass
        try:
            c["glow"].update()
        except:
            pass

    def _launch_custom_target(self, key, auto=False):
        info = self.custom_devices.get(key, {})
        c = self.cards.get(key, {})
        if not info or not c:
            return
        name = c.get("name_label").value if c.get("name_label") else key
        is_exe = bool(info.get("is_exe", c.get("_is_exe", False)))
        target = info.get("url")
        if is_exe:
            if self._is_winamp_target(target):
                if (not target) or (not os.path.exists(target)):
                    self.log(f"[Winamp] Path missing for '{name}' — searching likely install paths...", color="orange400")
                    _found = self._find_winamp_locally()
                    if _found and os.path.exists(_found):
                        self._set_winamp_path_from_picker(key, _found)
                        target = _found
                        self.log(f"[Winamp] Auto-detected path for '{name}'", color="green400")
                    else:
                        self.log(f"[Winamp] Path still unknown for '{name}' — opening setup options", color="orange400")
                        self._show_winamp_setup_dialog(key)
                        return
            if self._is_spotify_exe_target(target):
                if (not target) or (not os.path.exists(target)):
                    self.log(f"[Spotify] Path missing for '{name}' — searching likely install paths...", color="orange400")
                    _found = self._find_spotify_exe_locally()
                    if _found and os.path.exists(_found):
                        self._set_spotify_exe_path_from_picker(key, _found)
                        target = _found
                        self.log(f"[Spotify] Auto-detected path for '{name}'", color="green400")
                    else:
                        self.log(f"[Spotify] Path still unknown for '{name}' — opening setup options", color="orange400")
                        self._show_spotify_exe_setup_dialog(key)
                        return
            running_pid = self._find_running_exe_pid(target)
            if running_pid:
                self.custom_launch_state[key] = {
                    "kind": "exe", "pid": running_pid, "managed": False, "path": target
                }
                self._update_custom_card_launch_ui(key, True)
                self.log(f"[App] '{name}' already running (PID {running_pid})", color="cyan")
                return
            try:
                proc = subprocess.Popen([target])
                self.custom_launch_state[key] = {
                    "kind": "exe", "pid": proc.pid, "managed": True, "path": target
                }
                self._update_custom_card_launch_ui(key, True)
                if self._is_winamp_target(target):
                    self._queue_winamp_play(target)
                elif self._is_spotify_exe_target(target):
                    self._queue_spotify_desktop_play(key)
                prefix = "[Auto Start]" if auto else "[App]"
                self.log(f"{prefix} Launched '{name}' (PID {proc.pid})", color="green400")
            except Exception as ex:
                self.log(f"[App] Failed to launch '{name}': {ex}", color="red400")
            return

        running_pid = self._find_running_url_pid(key, target)
        if running_pid:
            self.custom_launch_state[key] = {
                "kind": "url", "pid": running_pid, "managed": False, "url": target
            }
            self._update_custom_card_launch_ui(key, True)
            self.log(f"[Web] '{name}' already open (PID {running_pid})", color="cyan")
            return

        if self._is_spotify_url_target(target):
            try:
                self._ensure_spotify_playback(key, target, auto=auto, allow_open=True, force_dedicated_open=True)
            except Exception as ex:
                self.log(f"[Web] Failed Spotify ensure-play for '{name}': {ex}", color="red400")
            return

        # URL cards open in normal browser mode (no managed profile).
        try:
            self.page.launch_url(target)
            self.custom_launch_state.pop(key, None)
            self._update_custom_card_launch_ui(key, False)
            prefix = "[Auto Start]" if auto else "[Web]"
            self.log(f"{prefix} Opened '{name}' in normal browser", color="green400")
        except Exception as ex:
            self.log(f"[Web] Failed to open '{name}': {ex}", color="red400")

    def _stop_custom_target(self, key, auto=False):
        info = self.custom_devices.get(key, {})
        c = self.cards.get(key, {})
        if not info or not c:
            return
        name = c.get("name_label").value if c.get("name_label") else key
        is_exe = bool(info.get("is_exe", c.get("_is_exe", False)))
        target = info.get("url")
        stopped = False

        if is_exe:
            target_norm = self._normalize_path(target)
            _spotify_exe_target = self._is_spotify_exe_target(target)
            for proc in psutil.process_iter(["pid", "exe", "cmdline"]):
                try:
                    pexe = proc.info.get("exe")
                    cmd = proc.info.get("cmdline") or []
                    matches = (pexe and self._normalize_path(pexe) == target_norm) or (cmd and self._normalize_path(cmd[0]) == target_norm)
                    if (not matches) and _spotify_exe_target:
                        _pname = ""
                        try:
                            _pname = (proc.name() or "").lower()
                        except Exception:
                            _pname = ""
                        if _pname == "spotify.exe":
                            matches = True
                    if not matches:
                        continue
                    proc.terminate()
                    try:
                        proc.wait(timeout=2)
                    except:
                        proc.kill()
                    stopped = True
                except:
                    continue
            self.custom_launch_state.pop(key, None)
            self._update_custom_card_launch_ui(key, False)
            if stopped:
                prefix = "[Auto Exit]" if auto else "[App]"
                self.log(f"{prefix} Closed '{name}'", color="orange400")
            else:
                self.log(f"[App] '{name}' was not running", color="grey500")
            return

        # Spotify URL cards: best-effort pause + close tab workflow (handles stale tabs).
        if self._is_spotify_url_target(target):
            try:
                if bool(self._spotify_play_state.get(key, False)):
                    self._send_spotify_command(key, "PAUSE")
                    self.log(f"[Web] Sent PAUSE to '{name}'", color="orange400")
                    _wait_end = time.monotonic() + 2.5
                    while self.running and (time.monotonic() < _wait_end):
                        if not bool(self._spotify_play_state.get(key, False)):
                            break
                        time.sleep(0.1)

                _closed = self._close_spotify_browser_windows()
                if _closed == 0:
                    _retry_end = time.monotonic() + 2.0
                    while self.running and (time.monotonic() < _retry_end) and _closed == 0:
                        time.sleep(0.25)
                        _closed = self._close_spotify_browser_windows()

                if _closed == 0 and self._close_foreground_browser_tab():
                    _closed = 1

                if _closed > 0:
                    self.log(f"[Web] Closed {int(_closed)} Spotify tab target(s) for '{name}'", color="orange400")
                else:
                    self.log(f"[Web] Spotify web UI not found for '{name}'", color="grey500")
            except Exception as ex:
                self.log(f"[Web] Spotify close flow failed for '{name}': {ex}", color="red400")

            self.custom_launch_state.pop(key, None)
            self._spotify_play_state[key] = False
            self._spotify_media_last_state = False
            self._spotify_keepalive_until.pop(key, None)
            self._spotify_window_seen_until = 0.0
            self._apply_spotify_track_metadata("", "")
            self._update_custom_card_launch_ui(key, False)
            return

        # URL card (normal browser mode): app does not own browser process.
        self.custom_launch_state.pop(key, None)
        self._spotify_play_state.pop(key, None)
        self._spotify_keepalive_until.pop(key, None)
        self._update_custom_card_launch_ui(key, False)
        self.log(f"[Web] '{name}' uses normal browser mode — close it manually", color="grey500")

    def _toggle_custom_target(self, key):
        c = self.cards.get(key)
        if not c:
            return
        if c.get("_is_active"):
            self._stop_custom_target(key, auto=False)
        else:
            self._launch_custom_target(key, auto=False)

    def _run_custom_autolaunches(self):
        # Give UI/cards time to render first.
        time.sleep(2.0)
        for key, info in list(self.custom_devices.items()):
            if not info.get("auto_launch_start"):
                continue
            if key not in self.cards:
                continue
            try:
                # Spotify auto-start behavior:
                # listener writes startup result to flag (None -> True/False), then
                # unified ensure-playback logic decides whether to play existing tab
                # or open a fresh one.
                if (not bool(info.get("is_exe", False))) and self._is_spotify_url_target(info.get("url", "")):
                    self._spotify_listener_loaded_at_start = None
                    _deadline = time.monotonic() + 4.0
                    while self.running and (time.monotonic() < _deadline) and (self._spotify_listener_loaded_at_start is None):
                        self._update_spotify_media_listener_gate()
                        time.sleep(0.25)

                    self._ensure_spotify_playback(key, info.get("url", ""), auto=True, allow_open=True)
                    continue

                self._launch_custom_target(key, auto=True)
            except Exception as ex:
                self.log(f"[Auto Start] Failed for '{info.get('name', key)}': {ex}", color="red400")

    def _custom_launcher_monitor_loop(self):
        # Periodically reconcile card state with external process state.
        time.sleep(3.0)
        while self.running:
            self._update_spotify_media_listener_gate()
            _winamp_track = self._get_winamp_now_playing_text()
            for key, c in list(self.cards.items()):
                if not c.get("_is_custom"):
                    continue
                info = self.custom_devices.get(key, {})
                is_exe = bool(info.get("is_exe", c.get("_is_exe", False)))
                target = info.get("url", c.get("_url"))
                if not target:
                    continue

                if self._is_winamp_target(target):
                    self._set_custom_card_media_text(key, _winamp_track)
                elif self._is_spotify_exe_target(target):
                    _track = (self._spotify_media_last_track or "").strip()
                    if not _track:
                        _track = (self._get_spotify_desktop_now_playing_text() or "").strip()
                    self._set_custom_card_media_text(key, _track)
                elif self._is_spotify_url_target(target):
                    _fresh_spot_track = (self._get_spotify_window_track_text() or "").strip()
                    if _fresh_spot_track:
                        self._spotify_media_last_track = _fresh_spot_track
                        _spot_track = _fresh_spot_track
                    elif self._spotify_is_active_now(key) or self._is_spotify_web_window_open():
                        _spot_track = (self._spotify_media_last_track or "").strip()
                    else:
                        _spot_track = ""
                    self._set_custom_card_media_text(key, _spot_track)

                try:
                    running_pid = self._find_running_exe_pid(target) if is_exe else self._find_running_url_pid(key, target)
                except:
                    running_pid = None
                active = bool(c.get("_is_active"))
                card_name = c.get("name_label").value if c.get("name_label") else key

                if active and not running_pid:
                    self.custom_launch_state.pop(key, None)
                    if self._is_spotify_url_target(target):
                        self._spotify_play_state[key] = False
                        self._spotify_keepalive_until.pop(key, None)
                        self._apply_spotify_track_metadata("", "")
                    self._update_custom_card_launch_ui(key, False)
                    self.log(f"[App] '{card_name}' closed outside app", color="grey500")
                elif (not active) and running_pid:
                    self.custom_launch_state[key] = {
                        "kind": "exe" if is_exe else "url",
                        "pid": running_pid,
                        "managed": False,
                        "path": target if is_exe else None,
                        "url": target if not is_exe else None,
                    }
                    self._update_custom_card_launch_ui(key, True)
                    self.log(f"[App] '{card_name}' detected running", color="grey500")
            time.sleep(4.0)

    def _run_custom_autoclose_on_exit(self):
        for key, info in list(self.custom_devices.items()):
            if not info.get("auto_close_exit"):
                continue
            # EXE cards can be closed; Spotify URL cards can be paused/stopped.
            if not bool(info.get("is_exe", False)):
                _url = info.get("url", "")
                if self._is_spotify_url_target(_url):
                    try:
                        if bool(self._spotify_play_state.get(key, False)):
                            self._send_spotify_command(key, "PAUSE")
                            self.log(f"[Auto Exit] Sent PAUSE to '{info.get('name', key)}'", color="orange400")
                            _wait_end = time.monotonic() + 2.5
                            while self.running and (time.monotonic() < _wait_end):
                                if not bool(self._spotify_play_state.get(key, False)):
                                    break
                                time.sleep(0.1)

                        _closed = self._close_spotify_browser_windows()
                        if _closed == 0:
                            _retry_end = time.monotonic() + 2.0
                            while self.running and (time.monotonic() < _retry_end) and _closed == 0:
                                time.sleep(0.25)
                                _closed = self._close_spotify_browser_windows()

                        if _closed > 0:
                            self.log(f"[Auto Exit] Closed {int(_closed)} Spotify tab target(s) for '{info.get('name', key)}'", color="orange400")
                        else:
                            if self._close_foreground_browser_tab():
                                self.log(f"[Auto Exit] Spotify title not found — closed foreground browser tab for '{info.get('name', key)}'", color="orange400")
                            else:
                                self.log(f"[Auto Exit] Spotify web UI not found for '{info.get('name', key)}'", color="grey500")
                    except Exception as ex:
                        self.log(f"[Auto Exit] Spotify pause failed for '{info.get('name', key)}': {ex}", color="red400")
                continue
            try:
                self._stop_custom_target(key, auto=True)
            except Exception as ex:
                self.log(f"[Auto Exit] Failed for '{info.get('name', key)}': {ex}", color="red400")

    def _add_custom_card(self, key, name, url, is_local, is_exe=False):
        """Build and add a custom launcher card matching standard card layout with drag support."""
        if key in self.cards: return

        # Restore is_exe from cache if not passed directly (e.g. on app restart)
        if not is_exe:
            is_exe = self.custom_devices.get(key, {}).get("is_exe", False)

        display_name = self.custom_names.get(key, name)
        is_winamp = bool(is_exe and self._is_winamp_target(url))
        is_spotify_web = bool((not is_exe) and self._is_spotify_url_target(url))
        is_spotify_exe = bool(is_exe and self._is_spotify_exe_target(url))
        name_label = ft.Text(display_name, weight="bold", size=16)
        status = ft.Text("CHECKING..." if is_local else "", size=12, color="grey500", weight="bold")
        status.visible = True
        info_text_val = "Now Playing: --" if (is_winamp or is_spotify_web or is_spotify_exe) else url
        info_text = ft.Text(
            info_text_val,
            size=10,
            color="grey500",
            max_lines=2,
            overflow=ft.TextOverflow.ELLIPSIS,
        )
        info_slot = ft.Container(
            content=info_text,
            height=26,
            alignment=ft.alignment.top_left,
        )

        edit_btn = ft.IconButton(ft.Icons.EDIT, icon_size=13, icon_color="grey500",
            tooltip="Rename", on_click=lambda _, k=key: self.show_rename_dialog(k))

        info = self.custom_devices.get(key, {})
        auto_launch_start = bool(info.get("auto_launch_start", False))
        auto_close_exit = bool(info.get("auto_close_exit", False))

        launch_btn_text = ft.Text("LAUNCH" if is_exe else "OPEN", size=11, weight="bold", color="white")
        launch_btn_icon = ft.Icon(ft.Icons.PLAY_ARROW if is_exe else ft.Icons.OPEN_IN_BROWSER, size=14, color="white")

        if is_exe:
            # Exe card — show program icon and launch/close button
            type_tag = ft.Container(
                content=ft.Icon(ft.Icons.TERMINAL, size=14, color="green400"),
                padding=ft.padding.symmetric(3, 5), border_radius=4,
                bgcolor="#1e1e2a", border=ft.border.all(1, "#2b2b3b"),
                tooltip=url,
            )
            action_btn = ft.ElevatedButton(
                content=ft.Row([launch_btn_icon, launch_btn_text], spacing=4, tight=True),
                bgcolor="#1a1a2e", color="white",
                on_click=lambda _, k=key: self._toggle_custom_target(k),
                style=ft.ButtonStyle(shape=ft.RoundedRectangleBorder(radius=6)),
            )
        else:
            # URL/web card — favicon and open/close button
            _domain = url.replace("https://","").replace("http://","").split("/")[0]
            favicon_url = f"https://t2.gstatic.com/faviconV2?client=SOCIAL&type=FAVICON&fallback_opts=TYPE,SIZE,URL&url=https://{_domain}&size=64"
            type_tag = ft.Container(
                content=ft.Image(src=favicon_url, width=16, height=16, fit=ft.ImageFit.CONTAIN,
                    error_content=ft.Icon(ft.Icons.LANGUAGE, size=14, color="grey500")),
                padding=ft.padding.symmetric(3, 5), border_radius=4,
                bgcolor="#1e1e2a", border=ft.border.all(1, "#2b2b3b"),
                tooltip=url,
            )
            action_btn = ft.ElevatedButton(
                content=ft.Row([launch_btn_icon, launch_btn_text], spacing=4, tight=True),
                bgcolor="#1a1a2e", color="white",
                on_click=lambda _, k=key: self._toggle_custom_target(k),
                style=ft.ButtonStyle(shape=ft.RoundedRectangleBorder(radius=6)),
            )

        auto_launch_cb = ft.Checkbox(
            label="AUTO START",
            value=auto_launch_start,
            scale=0.8,
            on_change=lambda e, k=key: self._set_custom_card_option(k, "auto_launch_start", e.control.value),
        )
        auto_close_cb = ft.Checkbox(
            label="AUTO CLOSE" if is_exe else ("STOP ON EXIT" if is_spotify_web else "AUTO CLOSE"),
            value=auto_close_exit,
            scale=0.8,
            on_change=lambda e, k=key: self._set_custom_card_option(k, "auto_close_exit", e.control.value),
        )

        compact_icon_btn_style = ft.ButtonStyle(
            padding=ft.padding.symmetric(horizontal=1, vertical=0),
        )
        compact_combo_btn_style = ft.ButtonStyle(
            padding=ft.padding.symmetric(horizontal=2, vertical=0),
        )

        winamp_controls = ft.Container(
            visible=is_winamp,
            content=ft.Row([
                ft.IconButton(ft.Icons.SKIP_PREVIOUS, icon_size=16, icon_color="cyan",
                              tooltip="Previous track",
                              on_click=lambda _, k=key: self._send_winamp_command(k, 40044, "PREV"),
                              style=compact_icon_btn_style),
                ft.IconButton(ft.Icons.PLAY_ARROW, icon_size=16, icon_color="cyan",
                              tooltip="Play",
                              on_click=lambda _, k=key: self._send_winamp_command(k, 40045, "PLAY"),
                              style=compact_icon_btn_style),
                ft.IconButton(ft.Icons.PAUSE, icon_size=16, icon_color="cyan",
                              tooltip="Pause",
                              on_click=lambda _, k=key: self._send_winamp_command(k, 40046, "PAUSE"),
                              style=compact_icon_btn_style),
                ft.IconButton(ft.Icons.STOP, icon_size=16, icon_color="cyan",
                              tooltip="Stop",
                              on_click=lambda _, k=key: self._send_winamp_command(k, 40047, "STOP"),
                              style=compact_icon_btn_style),
                ft.IconButton(ft.Icons.SKIP_NEXT, icon_size=16, icon_color="cyan",
                              tooltip="Next track",
                              on_click=lambda _, k=key: self._send_winamp_command(k, 40048, "NEXT"),
                              style=compact_icon_btn_style),
                ft.IconButton(ft.Icons.OPEN_IN_NEW, icon_size=16, icon_color="cyan",
                              tooltip="Show Winamp UI",
                              on_click=lambda _, k=key: self._show_winamp_ui(k),
                              style=compact_icon_btn_style),
            ], spacing=0, vertical_alignment=ft.CrossAxisAlignment.CENTER),
        )

        spotify_prev_btn = ft.IconButton(ft.Icons.SKIP_PREVIOUS, icon_size=16, icon_color="cyan",
            tooltip="Previous track",
            on_click=lambda _, k=key: self._send_spotify_command(k, "PREV"),
            style=compact_icon_btn_style,
            disabled=True)
        spotify_playpause_btn = ft.TextButton(
            tooltip="Play/Pause",
            on_click=lambda _, k=key: self._send_spotify_command(k, "PLAY_PAUSE"),
            style=compact_combo_btn_style,
            content=ft.Row([
                ft.Icon(ft.Icons.PLAY_ARROW, size=14, color="cyan"),
                ft.Text("/", size=11, color="cyan"),
                ft.Icon(ft.Icons.PAUSE, size=14, color="cyan"),
            ], spacing=2, tight=True),
            disabled=True,
        )
        spotify_next_btn = ft.IconButton(ft.Icons.SKIP_NEXT, icon_size=16, icon_color="cyan",
            tooltip="Next track",
            on_click=lambda _, k=key: self._send_spotify_command(k, "NEXT"),
            style=compact_icon_btn_style,
            disabled=True)
        spotify_show_ui_btn = ft.IconButton(ft.Icons.OPEN_IN_NEW, icon_size=16, icon_color="cyan",
            tooltip="Show Spotify web UI",
            on_click=lambda _, k=key: self._show_spotify_web_ui(k, maximize=True),
            style=compact_icon_btn_style,
            disabled=True)
        spotify_controls = ft.Container(
            visible=is_spotify_web,
            content=ft.Row([
                spotify_prev_btn,
                spotify_playpause_btn,
                spotify_next_btn,
                spotify_show_ui_btn,
            ], spacing=0, vertical_alignment=ft.CrossAxisAlignment.CENTER),
        )

        spotify_desktop_show_ui_btn = ft.IconButton(
            ft.Icons.OPEN_IN_NEW, icon_size=16, icon_color="cyan",
            tooltip="Show Spotify app",
            on_click=lambda _, k=key: self._show_spotify_desktop_ui(k),
            style=compact_icon_btn_style)
        spotify_desktop_playpause_btn = ft.TextButton(
            tooltip="Play/Pause",
            on_click=lambda _, k=key: self._send_spotify_desktop_command(k, "PLAY_PAUSE"),
            style=compact_combo_btn_style,
            content=ft.Row([
                ft.Icon(ft.Icons.PLAY_ARROW, size=14, color="cyan"),
                ft.Text("/", size=11, color="cyan"),
                ft.Icon(ft.Icons.PAUSE, size=14, color="cyan"),
            ], spacing=2, tight=True),
        )
        spotify_desktop_controls = ft.Container(
            visible=is_spotify_exe,
            content=ft.Row([
                ft.IconButton(ft.Icons.SKIP_PREVIOUS, icon_size=16, icon_color="cyan",
                              tooltip="Previous track",
                              on_click=lambda _, k=key: self._send_spotify_desktop_command(k, "PREV"),
                              style=compact_icon_btn_style),
                spotify_desktop_playpause_btn,
                ft.IconButton(ft.Icons.SKIP_NEXT, icon_size=16, icon_color="cyan",
                              tooltip="Next track",
                              on_click=lambda _, k=key: self._send_spotify_desktop_command(k, "NEXT"),
                              style=compact_icon_btn_style),
                spotify_desktop_show_ui_btn,
            ], spacing=0, vertical_alignment=ft.CrossAxisAlignment.CENTER),
        )

        # Match standard card layout exactly — 3 rows + drag handle
        card = ft.Container(
            data=key, bgcolor="#121420", border_radius=12,
            padding=ft.padding.only(left=10, right=10, top=7, bottom=7),
            content=ft.Column([
                # ROW 1: favicon tag | name | ✏ | ✕ | spacer | OPEN/CLOSE
                ft.Row([
                    type_tag, name_label, edit_btn,
                    ft.IconButton(ft.Icons.CLOSE, icon_size=13, icon_color="red400",
                        tooltip="Remove", on_click=lambda _, k=key: self._remove_custom_card(k)),
                    ft.Container(expand=True),
                    action_btn,
                ], vertical_alignment="center", spacing=3),
                # ROW 2: info + status (full-width line under header)
                ft.Row([
                    ft.Column([info_slot, status], spacing=1, expand=True),
                ], vertical_alignment="center", spacing=2),
                # ROW 3: transport controls (Winamp EXE, Spotify EXE, or Spotify URL cards)
                winamp_controls,
                spotify_desktop_controls,
                spotify_controls,
                # ROW 4: card options
                ft.Row(
                    [auto_launch_cb, auto_close_cb] if (is_exe or is_spotify_web) else [auto_launch_cb],
                    spacing=6,
                    vertical_alignment=ft.CrossAxisAlignment.CENTER,
                ),
            ], spacing=4),
        )

        glow = ft.Container(content=card, border_radius=13,
            border=ft.border.all(2, "#2b2b3b"), bgcolor="#121420", padding=2)

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
            "_is_exe": is_exe, "_is_active": False,
            "launch_btn": action_btn,
            "launch_btn_text": launch_btn_text,
            "launch_btn_icon": launch_btn_icon,
            "winamp_controls": winamp_controls,
            "spotify_desktop_controls": spotify_desktop_controls,
            "spotify_desktop_show_ui_btn": spotify_desktop_show_ui_btn,
            "spotify_controls": spotify_controls,
            "spotify_prev_btn": spotify_prev_btn,
            "spotify_playpause_btn": spotify_playpause_btn,
            "spotify_next_btn": spotify_next_btn,
            "spotify_show_ui_btn": spotify_show_ui_btn,
            "auto_launch_cb": auto_launch_cb,
            "auto_close_cb": auto_close_cb,
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

        # Initial running-state detection for launchers.
        try:
            if is_exe:
                running = self._find_running_exe_pid(url) is not None
            else:
                running = self._find_running_url_pid(key, url) is not None
            self._update_custom_card_launch_ui(key, running)
        except:
            pass

    def _set_custom_card_option(self, key, option, value):
        info = self.custom_devices.get(key)
        if not info:
            return
        info[option] = bool(value)
        self.save_cache()

    def _seed_default_custom_cards(self):
        """Seed Winamp/Spotify default cards once unless explicitly deleted by user."""
        _changed = False
        _defaults = [
            (DEFAULT_WINAMP_CARD_KEY, "WINAMP", "winamp.exe", False, True),
            (DEFAULT_SPOTIFY_CARD_KEY, "SPOTIFY.COM", "https://open.spotify.com/", False, False),
        ]

        for _key, _name, _url, _is_local, _is_exe in _defaults:
            _meta = self._default_custom_cards_meta.setdefault(_key, {"auto_created": False, "user_deleted": False})
            _meta.setdefault("auto_created", False)
            _meta.setdefault("user_deleted", False)

            if _key in self.custom_devices:
                if not bool(_meta.get("auto_created", False)):
                    _meta["auto_created"] = True
                    _changed = True
                continue

            if bool(_meta.get("user_deleted", False)):
                continue

            if not bool(_meta.get("auto_created", False)):
                self.custom_devices[_key] = {
                    "name": _name,
                    "url": _url,
                    "is_local": _is_local,
                    "is_exe": _is_exe,
                    "auto_launch_start": False,
                    "auto_close_exit": False,
                }
                self.custom_names.setdefault(_key, _name)
                _meta["auto_created"] = True
                _changed = True

        return _changed

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
            if not c.get("_is_active"):
                c["glow"].border = ft.border.all(2, "#2b2b3b" if online else "#5a0000")
                c["glow"].bgcolor = "#121420" if online else "#1a0505"
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
            if c.get("_is_active"):
                try:
                    self._stop_custom_target(key)
                except:
                    pass
            cell = c.get("cell")
            if cell and cell in self.device_list.controls:
                self.device_list.controls.remove(cell)
            self.cards.pop(key, None)
            self.custom_devices.pop(key, None)
            self.custom_launch_state.pop(key, None)
            self._spotify_play_state.pop(key, None)
            self._spotify_keepalive_until.pop(key, None)
            self.custom_names.pop(key, None)
            if key in self._default_custom_cards_meta:
                self._default_custom_cards_meta[key]["user_deleted"] = True
                self._default_custom_cards_meta[key]["auto_created"] = True
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
            # Scene snapshots for WLED should only use preset IDs selected
            # from this app's preset picker (no live-state fallback).
            state["ps"] = self.last_selected_preset.get(ip, -1)
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

        # Match the scene-edit list to current card layout order.
        order_index = {}
        for i, ctrl in enumerate(self.device_list.controls):
            key = getattr(ctrl, "data", None)
            if key is not None:
                order_index[key] = i
        rows_data.sort(key=lambda x: (order_index.get(x[0], 10**9), x[2]))

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

    def activate_scene(self, idx, source="manual", wait=False, timeout=None):
        """Restore all devices to the state saved in this scene."""
        scene = self.scenes[idx] if idx < len(self.scenes) else None
        if not scene:
            return
        done_event = threading.Event()
        result = {"failed": None}
        self.log(f"[Scene] Activating '{scene['name']}'...")
        # Reset old active scene border then set new one (refs is a list — one per layout row)
        old = self.active_scene_idx
        self.active_scene_idx = idx
        self.last_wled_scene_idx = idx
        self.save_cache()
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
                # Auto-restore at startup: devices may be slow to accept HTTP after ping;
                # use 3s per round (30s total) so slow-booting devices have time to respond.
                round_sleep = 3.0 if source == "auto" else 1.5
                tol_bri = 8             # brightness tolerance (0-255), ~8 ≈ 3%

                pending = {}            # ip -> scene state dict (ON and OFF targets)
                resend_count = {}       # ip -> resend attempts (debug)

                # ----------------------------
                # Small helpers
                # ----------------------------
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
                            _nm = self.cards.get(ip, {}).get("name_label")
                            _dname = _nm.value if _nm else ip
                            self.dbg_unique(f"scene_retry:{ip}",
                                f"[Scene][RETRY] {_dname} OFF (round {round_num})",
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
                    _nm = self.cards.get(ip, {}).get("name_label")
                    _dname = _nm.value if _nm else ip
                    self.dbg_unique(f"scene_retry:{ip}",
                        f"[Scene][RETRY] {_dname} ON (round {round_num})",
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
                    _nm = c.get("name_label")
                    name = _nm.value if _nm else ip
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
                            _nm = self.cards.get(ip, {}).get("name_label")
                            _dname = _nm.value if _nm else ip
                            self.dbg_unique(f"scene_ok:{ip}",
                                f"[Scene][OK] {_dname}",
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
                result["failed"] = failed

                if failed:
                    self.log(f"[Scene] '{scene_name}' — {len(failed)} device(s) failed / status unknown", color="red400")
                    def _get_failed_names(ip):
                        _nm = self.cards.get(ip, {}).get("name_label")
                        return _nm.value if _nm else ip
                    self.dbg_unique("scene_failed_list",
                        f"[Scene][DBG] Failed/unknown: {', '.join(_get_failed_names(ip) for ip in failed)}",
                        color="red400")
                    # On startup auto-restore, retry once if any devices failed (slow-boot devices
                    # may come up after the reconcile window — 30s gives them extra time to settle)
                    if source == "auto" and self.running and self.auto_restore_wled_scene:
                        def _retry_restore():
                            time.sleep(30)
                            if self.running and self.auto_restore_wled_scene:
                                self.log(f"[Scene Auto] Retrying WLED scene restore: '{scene_name}'...", color="cyan")
                                self.activate_scene(idx)  # plain retry, no further auto-retry
                        threading.Thread(target=_retry_restore, daemon=True).start()
                        self.log("[Scene Auto] Will retry in 30s...", color="orange400")
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
            finally:
                done_event.set()

                    
        threading.Thread(target=_apply, daemon=True).start()
        if wait:
            if done_event.wait(timeout):
                return result
            return None

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

    def show_edit_ip_dialog(self, ip):
        """Let the user type a new IP/hostname for a device card."""
        import re as _re
        status_text = ft.Text("", size=11, color="grey400")
        field = ft.TextField(
            value=ip,
            autofocus=True,
            border_color="cyan",
            hint_text="192.168.0.x  or  device.local",
            width=280,
            on_submit=lambda e: _do_save(e),
        )

        def _do_save(_):
            new_ip = field.value.strip().lower()
            if not new_ip or new_ip == ip:
                dlg.open = False
                self.page.update()
                return
            # Basic sanity: must look like an IP or hostname
            _looks_ok = (
                bool(_re.match(r'^\d+\.\d+\.\d+\.\d+$', new_ip))
                or new_ip.endswith(".local")
                or ("." in new_ip)
            )
            if not _looks_ok:
                status_text.value = "Enter a valid IP or hostname (e.g. 192.168.0.50)"
                status_text.color = "red400"
                try: status_text.update()
                except: pass
                return
            if new_ip in self.cards:
                status_text.value = f"A card for {new_ip} already exists"
                status_text.color = "orange400"
                try: status_text.update()
                except: pass
                return
            dlg.open = False
            self.page.update()
            self._reassign_ip(ip, new_ip, self.devices.get(ip, ip))

        def _cancel(_):
            dlg.open = False
            self.page.update()

        dlg = ft.AlertDialog(
            title=ft.Text("Edit Device IP", color="cyan"),
            content=ft.Column([
                ft.Text(f"Current IP: {ip}", size=11, color="grey500"),
                ft.Text("App will update live — some controls need a restart to fully re-bind.",
                        size=11, color="grey500"),
                field,
                status_text,
            ], tight=True, spacing=10, width=360),
            actions=[
                ft.ElevatedButton("Save", bgcolor="cyan", color="black", on_click=_do_save),
                ft.TextButton("Cancel", on_click=_cancel),
            ],
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
                self.save_cache()

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
                width=300,
                height=230,
            ),
            actions=[ft.TextButton("Cancel", on_click=lambda _: close_dlg(dlg))]
        )
        self.page.overlay.append(dlg)
        dlg.open = True
        self.page.update()

    def show_preset_picker(self, ip):
        """Popup list of WLED presets fetched from device."""
        def _load_and_show():
            def _first_playlist_child_id(entry):
                if not isinstance(entry, dict):
                    return None
                playlist = entry.get("playlist")
                seq = None
                if isinstance(playlist, dict):
                    seq = playlist.get("ps") or playlist.get("presets") or playlist.get("playlist")
                elif isinstance(playlist, list):
                    seq = playlist
                elif isinstance(entry.get("ps"), list):
                    seq = entry.get("ps")
                if not isinstance(seq, list) or not seq:
                    return None
                first = seq[0]
                if isinstance(first, dict):
                    first = first.get("ps", first.get("id", first.get("preset")))
                try:
                    return int(first)
                except:
                    return None

            try:
                raw = requests.get(f"http://{ip}/presets.json", timeout=6).json()
                presets = {k: v.get("n", f"Preset {k}") for k, v in raw.items()
                           if isinstance(v, dict) and v.get("n")}
                playlist_first = {}
                for k, v in raw.items():
                    child_id = _first_playlist_child_id(v)
                    if child_id is not None:
                        try:
                            playlist_first[int(k)] = child_id
                        except:
                            pass
                self.preset_cache[ip] = presets
                self.playlist_preset_first[ip] = playlist_first
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
                        # Keep a sticky record of the last preset choice so scene
                        # snapshots still capture playlist presets even if live state
                        # later reports ps=-1 while the playlist is running.
                        self.active_preset[ip] = int(pid)
                        self.last_selected_preset[ip] = int(pid)
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

            # Size picker to current window so it uses as much room as possible.
            _win_h = 0
            try:
                _win_h = int(getattr(getattr(self.page, "window", None), "height", 0) or 0)
            except:
                _win_h = 0
            if _win_h <= 0:
                _win_h = int(getattr(self.page, "height", 0) or 0)
            if _win_h <= 0:
                _win_h = 900
            _avail_h = max(240, int(_win_h * 0.82) - 120)
            _need_h = len(rows) * 52 + 20
            _list_h = min(_avail_h, _need_h)

            def close_preset(d):
                d.open = False
                self.page.update()

            dlg = ft.AlertDialog(
                title=ft.Text("Select Preset"),
                content=ft.Container(
                    content=ft.Column(rows, scroll=ft.ScrollMode.AUTO, spacing=0),
                    width=320,
                    height=_list_h,
                ),
                actions=[ft.TextButton("Cancel", on_click=lambda _: close_preset(dlg))]
            )
            self.page.overlay.append(dlg)
            dlg.open = True
            self.page.update()

        threading.Thread(target=_load_and_show, daemon=True).start()

    def show_mh_modes(self, ip):
        """MagicHome mode popup — select effect, use brightness slider for speed."""
        MODES = MH_MODES
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
                self.save_cache()
                self.send_magic_home_cmd(ip, [0x71, 0x23, 0x0F])
                self.log(f"{_cn} — Effect: STATIC ({ip})", color="cyan")
                self._mh_confirm_ping(ip)
                if ip in self.cards:
                    self.cards[ip]["bri_text"].value = f"{int((bri/255)*100)}%"
                    try: self.cards[ip]["bri_text"].update()
                    except: pass
            else:
                self.mh_mode[ip] = {"pattern": pattern, "speed": spd_byte}
                self.save_cache()
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

        # Size picker to current window so it uses as much room as possible.
        _win_h = 0
        try:
            _win_h = int(getattr(getattr(self.page, "window", None), "height", 0) or 0)
        except:
            _win_h = 0
        if _win_h <= 0:
            _win_h = int(getattr(self.page, "height", 0) or 0)
        if _win_h <= 0:
            _win_h = 900
        _avail_h = max(260, int(_win_h * 0.82) - 120)
        _mode_rows_h = len(MODES) * 56
        _header_h = 40  # helper text + divider + spacing
        _mode_list_h = min(max(220, _avail_h - _header_h), _mode_rows_h)

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
                    ], scroll=ft.ScrollMode.AUTO, height=_mode_list_h, spacing=0),
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
        _update_ver_text = ft.Text("", size=9, weight=ft.FontWeight.BOLD, color="black", text_align="center")
        update_btn = ft.Container(
            visible=False, bgcolor="yellow700", border_radius=5,
            padding=ft.padding.symmetric(horizontal=8, vertical=4),
            alignment=ft.alignment.center,
            ink=True,
            tooltip="Flash latest firmware",
            on_click=lambda _, i=ip: threading.Thread(target=self.push_ota_update, args=(i,), daemon=True).start(),
            content=ft.Column([
                ft.Text("UPDATE", size=9, weight=ft.FontWeight.BOLD, color="black", text_align="center"),
                _update_ver_text,
            ], spacing=0, tight=True, horizontal_alignment=ft.CrossAxisAlignment.CENTER),
        )
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
        power_switch = ft.Switch(
            value=False,
            active_color="cyan",
            on_change=lambda e: self.toggle_light(ip, e.control.value),
        )
        bri_slider = ft.Slider(
            min=1,
            max=255,
            value=128,
            expand=True,
            active_color="cyan",
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
            tooltip="Pick color",
            ink=True,
            on_click=lambda _, i=ip: self.show_color_picker(i),
        )

        # ── preset / mode button ──────────────────────────────────────────────
        preset_label = ft.Text("PRESET", size=7, color="#00f2ff", weight="bold",
                               max_lines=2, overflow="ellipsis", text_align="center")
        if is_wled:
            action_btn = ft.Container(
                width=54, height=54, border_radius=10,
                bgcolor="#1e2133",
                border=ft.border.only(top=ft.border.BorderSide(1, "white10")),
                shadow=[ft.BoxShadow(blur_radius=10, color=ft.Colors.with_opacity(0.4, "black"))],
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
                bgcolor="#1e2133",
                border=ft.border.only(top=ft.border.BorderSide(1, "white10")),
                shadow=[ft.BoxShadow(blur_radius=10, color=ft.Colors.with_opacity(0.4, "black"))],
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
                width=62, height=26,
                border_radius=6,
                tooltip="Reboot device",
                alignment=ft.alignment.center,
                ink=True,
                gradient=ft.LinearGradient(
                    begin=ft.alignment.top_center,
                    end=ft.alignment.bottom_center,
                    colors=["#6b0000", "#380000"],
                ),
                content=ft.Text("REBOOT", size=9, weight="bold", color="white"),
            ),
        )

        sanitize_btn = ft.GestureDetector(
            visible=is_wled,
            on_tap=lambda _, i=ip: None if i in self.live_ips else self.confirm_sanitize(i),
            mouse_cursor=ft.MouseCursor.CLICK,
            content=ft.Container(
                width=62, height=26,
                border_radius=6,
                tooltip="Sanitize presets",
                alignment=ft.alignment.center,
                ink=True,
                gradient=ft.LinearGradient(
                    begin=ft.alignment.top_center,
                    end=ft.alignment.bottom_center,
                    colors=["#887700", "#554400"],
                ),
                
                content=ft.Text("SANITIZE", size=9, weight="bold", color="white"),
            ),
        )

        # Center column — REBOOT stacked above SANITIZE with small gap
        _center_col = ft.Column([reboot_btn, sanitize_btn],
            spacing=4, tight=True, visible=is_wled)

        # ── card layout ───────────────────────────────────────────────────────
        card = ft.Container(
            data=ip, bgcolor="#121420", border_radius=12,
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
                        ft.GestureDetector(
                            on_tap=lambda _, i=ip: self.show_edit_ip_dialog(i),
                            mouse_cursor=ft.MouseCursor.CLICK,
                            content=ft.Text(ip, size=11, color="grey500",
                                            tooltip="Click to edit IP"),
                        ),
                        info_text,
                        status,
                    ], spacing=2, expand=True),
                    _center_col,
                    ft.Row([color_btn, action_btn], spacing=8),
                ], vertical_alignment="center", spacing=6),

                # ROW 3: update btn + live badge + full-width slider
                ft.Row([
                    update_btn,
                    live_badge,
                    bri_slider,
                    ft.Container(content=bri_text, width=54, alignment=ft.alignment.center_right),
                ], spacing=6, vertical_alignment="center"),

            ], spacing=6)
        )

        glow = ft.Container(content=card, border_radius=13,
            border=ft.border.all(2, "#2b2b3b"), bgcolor="#121420", padding=2)

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
            "info_text": info_text, "update_btn": update_btn, "update_ver_text": _update_ver_text,
            "sanitize_btn": sanitize_btn, "reboot_btn": reboot_btn, "edit_btn": edit_btn,
            "color_btn": color_btn, "action_btn": action_btn,
            "live_badge": live_badge, "live_icon": _live_icon, "live_text": _live_text,
        }
        if not is_wled:
            self._apply_cached_mh_ui(ip)
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
        c["update_btn"].opacity = 0.5
        c["update_ver_text"].value = "UPDATING..."
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
            _cn = c.get("name_label")
            _cname = _cn.value if _cn else ip
            self.log(f"[OTA] {_cname}, {ip} — FAILED: {ex}", color="red400")
        finally:
            # Only reached on error paths (success returns early above)
            c["update_btn"].disabled = False
            c["update_btn"].opacity = 1.0
            c["update_ver_text"].value = f"v{self.latest_release_ver}" if self.latest_release_ver else ""
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
                        c["update_btn"].opacity = 1.0
                        try: c["update_btn"].update()
                        except: pass
                    return
            except:
                pass
            self.log(f"[OTA] Device offline, retrying... ({attempt+1}/15)")
            time.sleep(4)
        self.log(f"[OTA] {ip} did not come back online after 60s. Check device manually.", color="red400")
        c["update_btn"].disabled = False
        c["update_btn"].opacity = 1.0
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
                _bri = max(0.25, self.border_speed / 20.0)
                border_color = self._dim_hex(self.border_color, _bri)
            elif ef == "breathing":
                self._breath_border += 0.05 * self.border_speed / 4.0 * self._breath_border_dir
                if self._breath_border >= 1.0:
                    self._breath_border = 1.0; self._breath_border_dir = -1
                elif self._breath_border <= 0.25:
                    self._breath_border = 0.25; self._breath_border_dir = 1
                border_color = self._dim_hex(self.border_color, self._breath_border)
            elif ef == "strobe":
                self._strobe_border = not self._strobe_border
                border_color = self.border_color if self._strobe_border else "#000000"
            else:
                border_color = self._hue_to_hex(_border_hue)

            # Apply border to all ON/live cards with grid-position-aware effects
            # Build ordered list matching device_list visual order
            # Custom launcher cards join border animation only while active.
            # Offline WLED/MH cards stay red and are excluded.
            _ordered = []
            for ctrl in self.device_list.controls:
                ip = getattr(ctrl, "data", None)
                if ip and ip in self.cards:
                    c = self.cards[ip]
                    if (c.get("_is_custom") and c.get("_is_active")) or c.get("_glow_state") == "on" or ip in self.live_ips:
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
                        _c = self._hue_to_hex((_border_hue - _col * _spread) % 360)
                    elif ef == "wave_tb":
                        # Wave travels top to bottom — offset by row
                        _spread = 300 / max(_rows - 1, 1)
                        _c = self._hue_to_hex((_border_hue - _row * _spread) % 360)
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

            # Animate active LedFx scene button border
            led_active = self.active_ledfx_scene_id
            if led_active is not None and led_active in self.ledfx_scene_btn_refs:
                _sc = border_color if border_color else self._hue_to_hex(_border_hue)
                for ref in self.ledfx_scene_btn_refs[led_active]:
                    try:
                        ref.border = ft.border.all(1, _sc)
                        ref.update()
                    except:
                        pass

            # Spectrum box border follows app border color while audio is active.
            try:
                _now = time.monotonic()
                _spec_c = border_color if border_color else self._hue_to_hex(_border_hue)
                _audio_recent = (_now - float(getattr(self, "_spec_last_audio_ts", 0.0))) <= 1.0
                _active_audio = _audio_recent and (not bool(getattr(self, "_spec_idle_active", False)))
                if _active_audio:
                    self._spectrum_box.border = ft.border.all(2, _spec_c)
                else:
                    self._spectrum_box.border = ft.border.all(1, self._dim_hex(_spec_c, 0.55))
                self._spectrum_box.update()
            except Exception:
                pass

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
                    _bri = max(0.25, self.title_speed / 20.0)
                    _c = self._dim_hex(self.title_color, _bri)
                    for _tc in self._title_chars:
                        _tc.color = _c
                elif tef == "breathing":
                    self._breath_title += 0.05 * self.title_speed / 4.0 * self._breath_title_dir
                    if self._breath_title >= 1.0:
                        self._breath_title = 1.0; self._breath_title_dir = -1
                    elif self._breath_title <= 0.25:
                        self._breath_title = 0.25; self._breath_title_dir = 1
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

    def _set_spectrum_render_mode(self, mode):
        """Switch analyzer surface between pixel-grid mode and regular graphics mode."""
        _target = "graphics" if str(mode).lower() == "graphics" else "grid"
        if self._spec_render_mode == _target:
            return

        if _target == "graphics":
            self._spectrum_box.padding = ft.padding.all(0)
            self._spectrum_box.width = self._spec_box_graphics_size[0]
            self._spectrum_box.height = self._spec_box_graphics_size[1]
            self._spectrum_box.content = self._spec_graphics_host
            self._spec_graphics_ready = False
            self._spec_graphics_view_size = (0, 0)
        else:
            self._spectrum_box.padding = ft.padding.symmetric(horizontal=6, vertical=4)
            self._spectrum_box.width = self._spec_box_grid_size[0]
            self._spectrum_box.height = self._spec_box_grid_size[1]
            self._spectrum_box.content = self._spec_grid_content

        self._spec_render_mode = _target
        try:
            self._spectrum_box.update()
        except Exception:
            pass

    def _sync_spec_quick_buttons(self):
        try:
            _on = "#ff9800"
            _off = "grey500"
            self._spec_settings_btn.icon_color = _on
            self._spec_settings_btn.tooltip = "Spectrum settings"

            if getattr(self, "_spec_sampling_enabled", True):
                self._spec_sampling_btn.icon = ft.Icons.MIC
                self._spec_sampling_btn.icon_color = _on
                self._spec_sampling_btn.tooltip = "Sampling ON"
                self._spec_sampling_btn.style = ft.ButtonStyle(
                    bgcolor="transparent",
                    shape=ft.RoundedRectangleBorder(radius=5),
                    padding=ft.padding.all(1),
                )
            else:
                self._spec_sampling_btn.icon = ft.Icons.MIC
                self._spec_sampling_btn.icon_color = _off
                self._spec_sampling_btn.tooltip = "Sampling OFF"
                self._spec_sampling_btn.style = ft.ButtonStyle(
                    bgcolor="transparent",
                    shape=ft.RoundedRectangleBorder(radius=5),
                    padding=ft.padding.all(1),
                )

            if getattr(self, "_spec_idle_enabled", True):
                self._spec_idle_quick_btn.icon = ft.Icons.AUTO_AWESOME
                self._spec_idle_quick_btn.icon_color = _on
                self._spec_idle_quick_btn.tooltip = "Idle effects ON"
                self._spec_idle_quick_btn.style = ft.ButtonStyle(
                    bgcolor="transparent",
                    shape=ft.RoundedRectangleBorder(radius=5),
                    padding=ft.padding.all(1),
                )
            else:
                self._spec_idle_quick_btn.icon = ft.Icons.AUTO_AWESOME
                self._spec_idle_quick_btn.icon_color = _off
                self._spec_idle_quick_btn.tooltip = "Idle effects OFF"
                self._spec_idle_quick_btn.style = ft.ButtonStyle(
                    bgcolor="transparent",
                    shape=ft.RoundedRectangleBorder(radius=5),
                    padding=ft.padding.all(1),
                )

            self._spec_sampling_btn.update()
            self._spec_idle_quick_btn.update()
            self._spec_settings_btn.update()
        except Exception:
            pass

    def _clear_spectrum_display(self):
        """Leave the analyzer visible but static (no active bars/animation)."""
        try:
            self._set_spectrum_render_mode("grid")
            for _segs in self._spec_segments:
                for _seg in _segs:
                    _seg.bgcolor = "#101010"
            self._spectrum_box.update()
        except Exception:
            pass

    def _get_spec_render_interval(self):
        try:
            _fps = int(round(float(getattr(self, "_spec_target_fps", 25) or 25)))
        except Exception:
            _fps = 25
        _fps = max(8, min(30, _fps))
        return 1.0 / float(_fps)

    def _reset_spec_analysis_state(self):
        _count = max(6, min(int(self._spec_bands), int(getattr(self, "_spec_analysis_bands", self._spec_bands) or self._spec_bands)))
        self._spec_bars = [0.0] * _count
        self._spec_peaks = [0.0] * _count
        self._spec_peak_hold = [0] * _count
        self._spec_band_avg = [0.0] * _count

    def _set_spec_analysis_bands(self, bands, restart_audio=True, reset_now=False):
        try:
            _new = int(round(float(bands)))
        except Exception:
            _new = int(self._spec_bands)
        _new = max(6, min(int(self._spec_bands), _new))
        _old = int(getattr(self, "_spec_analysis_bands", self._spec_bands) or self._spec_bands)
        self._spec_analysis_bands = _new
        if reset_now:
            self._reset_spec_analysis_state()
        if restart_audio and (_new != _old):
            self._spec_source_changed = True
            if self._spec_disabled:
                self._spec_disabled = False
                threading.Thread(target=self._audio_analyzer_loop, daemon=True).start()
        return _new != _old

    def _toggle_spec_sampling(self, _=None):
        self._spec_sampling_enabled = not bool(getattr(self, "_spec_sampling_enabled", True))
        self._spec_source_changed = True
        if self._spec_disabled:
            self._spec_disabled = False
            threading.Thread(target=self._audio_analyzer_loop, daemon=True).start()
        self._sync_spec_quick_buttons()
        self.log(f"[Spectrum] Sampling {'ON' if self._spec_sampling_enabled else 'OFF'}", color="grey500")

    def _toggle_spec_idle_quick(self, _=None):
        self._spec_idle_enabled = not bool(getattr(self, "_spec_idle_enabled", True))
        self._spec_idle_active = False
        self._sync_spec_quick_buttons()
        if (not self._spec_sampling_enabled) and (not self._spec_idle_enabled):
            self._clear_spectrum_display()
            self._spec_display_cleared = True
        self.log(f"[Spectrum] Idle effects {'ON' if self._spec_idle_enabled else 'OFF'}", color="grey500")

    def _ensure_spectrum_graphics_controls(self, width, height):
        """Create/update reusable controls for non-grid spectrum graphics effects."""
        _w = max(120, int(width))
        _h = max(80, int(height))
        _size = (_w, _h)
        if self._spec_graphics_ready and self._spec_graphics_view_size == _size:
            return

        self._spec_graphics_layer.controls.clear()
        self._spec_graphics_stars = []
        self._spec_graphics_lines = []

        _rng = random.Random(0x51A7)
        _star_count = max(24, min(96, int((_w * _h) / 2200)))
        for _ in range(_star_count):
            _dot = ft.Container(
                left=_rng.randint(0, max(0, _w - 3)),
                top=_rng.randint(0, max(0, _h - 3)),
                width=2,
                height=2,
                border_radius=1,
                bgcolor="#6a6a6a",
                opacity=0.45,
            )
            self._spec_graphics_stars.append(_dot)
            self._spec_graphics_layer.controls.append(_dot)

        for _ in range(18):
            _txt = ft.Text(
                "",
                size=12,
                color="#ffd76a",
                text_align=ft.TextAlign.CENTER,
                no_wrap=True,
                weight=ft.FontWeight.W_600,
            )
            _slot = ft.Container(
                content=_txt,
                left=0,
                top=0,
                width=1,
                height=1,
                alignment=ft.alignment.center,
                visible=False,
            )
            self._spec_graphics_lines.append((_slot, _txt))
            self._spec_graphics_layer.controls.append(_slot)

        self._spec_graphics_ready = True
        self._spec_graphics_view_size = _size

    def _render_spectrum(self):
        if not self._spec_segments:
            return

        if self._spec_idle_active:
            _idle_fx = str(self._spec_idle_effect or "random").lower()
            if _idle_fx == "random":
                _now = time.monotonic()
                if _now >= float(self._spec_idle_random_next_ts):
                    _choices = list(getattr(self, "_spec_idle_cycle_effects", []))
                    if not _choices:
                        _choices = ["aurora", "pulse", "text", "rainbow", "pacman", "tetris", "invaders", "snake", "starwars"]
                    if self._spec_idle_random_current in _choices and len(_choices) > 1:
                        _choices = [x for x in _choices if x != self._spec_idle_random_current]
                    self._spec_idle_random_current = random.choice(_choices)
                    self._spec_idle_random_next_ts = _now + max(0.1, float(self._spec_idle_random_cycle_seconds))
                _idle_fx = self._spec_idle_random_current

            if _idle_fx == "starwars":
                self._set_spectrum_render_mode("graphics")
                self._render_spectrum_idle_starwars()
                return

            self._set_spectrum_render_mode("grid")
            if _idle_fx == "text":
                self._render_spectrum_idle_text()
            elif _idle_fx == "pulse":
                self._render_spectrum_idle_pulse()
            elif _idle_fx == "rainbow":
                self._render_spectrum_idle_rainbow_wave()
            elif _idle_fx == "pacman":
                self._render_spectrum_idle_pacman()
            elif _idle_fx == "tetris":
                self._render_spectrum_idle_tetris()
            elif _idle_fx == "invaders":
                self._render_spectrum_idle_invaders()
            elif _idle_fx == "snake":
                self._render_spectrum_idle_snake()
            else:
                self._render_spectrum_idle_aurora()
            return

        self._set_spectrum_render_mode("grid")

        _mode = str(self._spec_mode or "classic").lower()
        if _mode == "random":
            _now = time.monotonic()
            if _now >= float(self._spec_mode_random_next_ts):
                self._advance_spectrum_random_mode()
                self._spec_mode_random_next_ts = _now + max(1.0, float(self._spec_mode_random_cycle_seconds))
            _mode = self._spec_mode_random_current
        elif _mode == "random_song":
            _now = time.monotonic()
            if self._spec_mode_song_switch_armed and ((_now - float(self._spec_last_audio_ts)) >= float(self._spec_mode_song_silence_seconds)):
                self._advance_spectrum_random_mode()
                self._spec_mode_song_switch_armed = False
            _mode = self._spec_mode_random_current

        if _mode == "vu":
            self._render_spectrum_vu()
        else:
            # Classic mode: vertical bars, left to right
            self._render_spectrum_classic()

        try:
            self._spectrum_box.update()
        except Exception:
            pass

    def _advance_spectrum_random_mode(self):
        _choices = ["classic", "vu"]
        if self._spec_mode_random_current in _choices and len(_choices) > 1:
            _choices = [x for x in _choices if x != self._spec_mode_random_current]
        self._spec_mode_random_current = random.choice(_choices)

    def _render_spectrum_classic(self):
        """Classic mode: vertical bars from bottom-up, left to right."""
        _analysis_count = max(1, len(self._spec_bars))
        for bi, segs in enumerate(self._spec_segments):
            _src_i = min(_analysis_count - 1, int((bi * _analysis_count) / max(1, self._spec_bands)))
            fill = int(max(0.0, min(1.0, self._spec_bars[_src_i])) * self._spec_levels)
            peak = int(max(0.0, min(1.0, self._spec_peaks[_src_i])) * (self._spec_levels - 1))

            for top_idx, seg in enumerate(segs):
                lvl_from_bottom = self._spec_levels - 1 - top_idx
                if lvl_from_bottom == peak:
                    seg.bgcolor = "#ff2020"
                elif lvl_from_bottom < fill:
                    seg.bgcolor = self._spec_palette[lvl_from_bottom]
                else:
                    seg.bgcolor = "#101010"

    def _render_spectrum_mirror(self):
        """Mirror mode: uses all pixels, center-reflected spectrum layout."""
        _center_col = self._spec_bands // 2
        _max_height = self._spec_levels - 1
        
        for bi, segs in enumerate(self._spec_segments):
            # Distance from center column determines which band's data to show
            _dist = abs(bi - _center_col)
            if _dist < self._spec_bands:
                _idx = _dist
                bar_val = max(0.0, min(1.0, self._spec_bars[_idx]))
                peak_val = max(0.0, min(1.0, self._spec_peaks[_idx]))
                
                _bar_height = int(round(bar_val * _max_height))
                _peak_height = int(round(peak_val * _max_height))
                
                for top_idx, seg in enumerate(segs):
                    _from_bottom = self._spec_levels - 1 - top_idx
                    
                    if _from_bottom == _peak_height and _peak_height > 0:
                        seg.bgcolor = "#ff2020"
                    elif _from_bottom <= _bar_height and _bar_height > 0:
                        seg.bgcolor = self._spec_palette[min(_from_bottom, len(self._spec_palette) - 1)]
                    else:
                        seg.bgcolor = "#101010"
            else:
                for seg in segs:
                    seg.bgcolor = "#101010"

    def _render_spectrum_vu(self):
        """VU mode: two horizontal lanes (top=L, bottom=R) with right-side labels."""
        _bg = "#101010"
        _bands = max(1, self._spec_bands)

        _meter_start = 0
        _meter_end = max(_meter_start + 1, _bands - 3)  # rightmost 3 columns reserved for labels
        _meter_width = max(1, _meter_end - _meter_start)

        _l_fill = int(round(max(0.0, min(1.0, self._spec_vu_left)) * _meter_width))
        _r_fill = int(round(max(0.0, min(1.0, self._spec_vu_right)) * _meter_width))
        _l_peak = int(round(max(0.0, min(1.0, self._spec_vu_peak_left)) * _meter_width))
        _r_peak = int(round(max(0.0, min(1.0, self._spec_vu_peak_right)) * _meter_width))

        # Two lane layout across full height: upper lane for L, lower lane for R.
        _top_lane_rows = list(range(2, min(self._spec_levels, 7)))
        _bot_lane_rows = list(range(max(0, self._spec_levels - 7), self._spec_levels - 2))
        _top_mid = int((min(_top_lane_rows) + max(_top_lane_rows)) / 2) if _top_lane_rows else 3
        _bot_mid = int((min(_bot_lane_rows) + max(_bot_lane_rows)) / 2) if _bot_lane_rows else (self._spec_levels - 4)
        _top_peak_rows = _top_lane_rows[:5] if len(_top_lane_rows) >= 5 else _top_lane_rows
        _bot_peak_rows = _bot_lane_rows[-5:] if len(_bot_lane_rows) >= 5 else _bot_lane_rows

        for bi, segs in enumerate(self._spec_segments):
            for seg in segs:
                seg.bgcolor = _bg

            if bi < _meter_end:
                _x = bi - _meter_start
                _color_idx = int((_x / max(1, _meter_width - 1)) * (len(self._spec_palette) - 1))
                _color = self._spec_palette[min(_color_idx, len(self._spec_palette) - 1)]

                # Draw vertical dash lines in each lane so it reads like VU columns.
                if _x < _l_fill:
                    for _row in _top_lane_rows:
                        segs[_row].bgcolor = _color
                if _x < _r_fill:
                    for _row in _bot_lane_rows:
                        segs[_row].bgcolor = _color

                if _x == _l_peak and _l_peak > 0:
                    for _row in _top_peak_rows:
                        if 0 <= _row < self._spec_levels:
                            segs[_row].bgcolor = "#ff2020"
                if _x == _r_peak and _r_peak > 0:
                    for _row in _bot_peak_rows:
                        if 0 <= _row < self._spec_levels:
                            segs[_row].bgcolor = "#ff2020"
            else:
                # Compact right-side labels (3x5): L in upper section, R in lower section.
                _label_start = max(0, _bands - 3)
                _gx = bi - _label_start

                _l_rows = ["100", "100", "100", "100", "111"]
                _r_rows = ["110", "101", "110", "101", "101"]
                _l_row0 = 1
                _r_row0 = max(0, self._spec_levels - 6)

                if 0 <= _gx < 3:
                    for _ry in range(5):
                        _row = _l_row0 + _ry
                        if 0 <= _row < self._spec_levels and _l_rows[_ry][_gx] == "1":
                            segs[_row].bgcolor = "#8a8a8a"
                    for _ry in range(5):
                        _row = _r_row0 + _ry
                        if 0 <= _row < self._spec_levels and _r_rows[_ry][_gx] == "1":
                            segs[_row].bgcolor = "#8a8a8a"

    def _build_spec_text_columns(self, text):
        # 5x7 glyphs for idle marquee text.
        _font = {
            " ": ["00000", "00000", "00000", "00000", "00000", "00000", "00000"],
            "A": ["01110", "10001", "10001", "11111", "10001", "10001", "10001"],
            "C": ["01110", "10001", "10000", "10000", "10000", "10001", "01110"],
            "E": ["11111", "10000", "10000", "11110", "10000", "10000", "11111"],
            "L": ["10000", "10000", "10000", "10000", "10000", "10000", "11111"],
            "M": ["10001", "11011", "10101", "10101", "10001", "10001", "10001"],
            "N": ["10001", "11001", "10101", "10011", "10001", "10001", "10001"],
            "P": ["11110", "10001", "10001", "11110", "10000", "10000", "10000"],
            "R": ["11110", "10001", "10001", "11110", "10100", "10010", "10001"],
            "S": ["01111", "10000", "10000", "01110", "00001", "00001", "11110"],
            "T": ["11111", "00100", "00100", "00100", "00100", "00100", "00100"],
            "U": ["10001", "10001", "10001", "10001", "10001", "10001", "01110"],
            "Y": ["10001", "10001", "01010", "00100", "00100", "00100", "00100"],
            "Z": ["11111", "00001", "00010", "00100", "01000", "10000", "11111"],
            "D": ["11100", "10010", "10001", "10001", "10001", "10010", "11100"],
            "F": ["11111", "10000", "10000", "11110", "10000", "10000", "10000"],
            "G": ["01110", "10001", "10000", "10111", "10001", "10001", "01110"],
            "H": ["10001", "10001", "10001", "11111", "10001", "10001", "10001"],
            "I": ["11111", "00100", "00100", "00100", "00100", "00100", "11111"],
            "O": ["01110", "10001", "10001", "10001", "10001", "10001", "01110"],
            "W": ["10001", "10001", "10001", "10101", "10101", "11011", "10001"],
            "X": ["10001", "10001", "01010", "00100", "01010", "10001", "10001"],
            "+": ["00000", "00100", "00100", "11111", "00100", "00100", "00000"],
            ".": ["00000", "00000", "00000", "00000", "00000", "00110", "00110"],
        }
        _rows = [""] * 7
        for _ch in str(text).upper():
            _glyph = _font.get(_ch, _font[" "])
            for _r in range(7):
                _rows[_r] += _glyph[_r] + "0"
        _cols = []
        for _x in range(len(_rows[0]) if _rows and _rows[0] else 0):
            _col = [(_rows[_y][_x] == "1") for _y in range(7)]
            _cols.append(_col)
        return _cols

    def _render_spectrum_idle_text(self):
        if not self._spec_segments:
            return

        _cols = self._build_spec_text_columns(self._spec_idle_text)
        if not _cols:
            return

        # Scroll text at a speed controlled by idle speed slider.
        _spd = max(0.25, min(3.0, float(self._spec_idle_speed)))
        self._spec_idle_phase += 0.18 * _spd
        while self._spec_idle_phase >= 1.0:
            self._spec_idle_phase -= 1.0
            self._spec_idle_scroll = (self._spec_idle_scroll + 1) % len(_cols)

        _y_off = max(0, (self._spec_levels - 7) // 2)
        _bg = "#101010"
        for bi, segs in enumerate(self._spec_segments):
            _cx = (bi + self._spec_idle_scroll) % len(_cols)
            _bits = _cols[_cx]
            _color = self._spec_palette[(bi + int(self._spec_idle_scroll / 2)) % len(self._spec_palette)]
            for top_idx, seg in enumerate(segs):
                _y = top_idx - _y_off
                if 0 <= _y < 7 and _bits[_y]:
                    seg.bgcolor = _color
                else:
                    seg.bgcolor = _bg

        try:
            self._spectrum_box.update()
        except Exception:
            pass

    def _render_spectrum_idle_aurora(self):
        """Ambient idle effect: flowing multi-layer wave bands across the full grid."""
        if not self._spec_segments:
            return

        _bg = "#101010"
        _bands = max(1, self._spec_bands)
        _levels = max(1, self._spec_levels)
        _spd = max(0.25, min(3.0, float(self._spec_idle_speed)))

        # Reuse idle phase to animate smooth horizontal drift.
        self._spec_idle_phase += 0.07 * _spd
        if self._spec_idle_phase >= 1000.0:
            self._spec_idle_phase = 0.0

        _p = self._spec_idle_phase
        for bi, segs in enumerate(self._spec_segments):
            # Two moving centers create a layered ambient ribbon.
            _c1 = int((_levels - 1) * (((bi * 1.4 + _p * 7.0) % _bands) / max(1, _bands - 1)))
            _c2 = int((_levels - 1) * (((bi * 0.8 - _p * 4.0) % _bands) / max(1, _bands - 1)))
            _color = self._spec_palette[(bi + int(_p * 6.0)) % len(self._spec_palette)]

            for top_idx, seg in enumerate(segs):
                _dist1 = abs(top_idx - _c1)
                _dist2 = abs(top_idx - _c2)

                # Soft ribbon with brighter core and dim outer halo.
                if _dist1 <= 1 or _dist2 <= 1:
                    seg.bgcolor = _color
                elif _dist1 <= 2 or _dist2 <= 2:
                    seg.bgcolor = "#2a2a2a"
                else:
                    seg.bgcolor = _bg

            # Add subtle deterministic sparkle for extra life.
            _spark_row = int((bi * 3 + int(_p * 25)) % _levels)
            if ((bi + int(_p * 13)) % 11) == 0:
                segs[_spark_row].bgcolor = "#c8c8c8"

        try:
            self._spectrum_box.update()
        except Exception:
            pass

    def _render_spectrum_idle_pulse(self):
        """Ambient idle effect: expanding pulse rings with soft glow."""
        if not self._spec_segments:
            return

        _bg = "#101010"
        _bands = max(1, self._spec_bands)
        _levels = max(1, self._spec_levels)
        _spd = max(0.25, min(3.0, float(self._spec_idle_speed)))

        self._spec_idle_phase += 0.11 * _spd
        if self._spec_idle_phase >= 1000.0:
            self._spec_idle_phase = 0.0

        _p = self._spec_idle_phase
        _cx = (_bands - 1) / 2.0
        _cy = (_levels - 1) / 2.0
        # Let pulses travel fully off-screen, then recycle.
        _max_dist = ((_cx * _cx) + (_cy * _cy)) ** 0.5 + 2.0
        _spawn_gap = max(2.0, _max_dist * 0.65)  # second pulse starts before first exits
        _cycle = _max_dist + _spawn_gap
        _r1 = (_p * 0.9) % _cycle
        _r2 = (_r1 - _spawn_gap) % _cycle

        for bi, segs in enumerate(self._spec_segments):
            for top_idx, seg in enumerate(segs):
                _dx = bi - _cx
                _dy = top_idx - _cy
                _d = (_dx * _dx + _dy * _dy) ** 0.5
                _best = 999.0
                for _r in (_r1, _r2):
                    if _r <= _max_dist + 0.6:
                        _best = min(_best, abs(_d - _r))

                if _best < 0.55:
                    _idx = (bi + int(_p * 9.0)) % len(self._spec_palette)
                    seg.bgcolor = self._spec_palette[_idx]
                elif _best < 1.2:
                    seg.bgcolor = "#2a2a2a"
                else:
                    seg.bgcolor = _bg

            # subtle star flicker
            _spark_row = int((bi * 5 + int(_p * 17)) % _levels)
            if ((bi + int(_p * 8)) % 13) == 0:
                segs[_spark_row].bgcolor = "#b0b0b0"

        try:
            self._spectrum_box.update()
        except Exception:
            pass

    def _render_spectrum_idle_rainbow_wave(self):
        """Idle effect: all bars lit with a rainbow wave scrolling right-to-left."""
        if not self._spec_segments:
            return

        _spd = max(0.25, min(3.0, float(self._spec_idle_speed)))

        # Straight row-by-row hue sweep: each row has a fixed phase offset,
        # while columns carry a linear gradient that drifts right-to-left.
        self._spec_idle_phase = (self._spec_idle_phase + (5.0 * _spd)) % 360.0

        _col_step = 12.0  # hue delta per column
        _row_step = 20.0  # hue delta per row (offset between rows)
        _phase = self._spec_idle_phase

        try:
            for bi, segs in enumerate(self._spec_segments):
                for top_idx, seg in enumerate(segs):
                    _h = (_phase + (bi * _col_step) + (top_idx * _row_step)) % 360.0
                    seg.bgcolor = self._hue_to_hex(_h)
        except Exception:
            # Never let an idle effect freeze the analyzer; fallback to aurora.
            self._render_spectrum_idle_aurora()
            return

        try:
            self._spectrum_box.update()
        except Exception:
            pass

    def _render_spectrum_idle_pacman(self):
        """Idle effect: Pac-Man chasing a ghost across the analyzer grid."""
        if not self._spec_segments:
            return

        _bands = max(1, self._spec_bands)
        _levels = max(1, self._spec_levels)
        _spd = max(0.25, min(3.0, float(self._spec_idle_speed)))
        _bg = "#101010"

        # Horizontal track includes off-screen padding so sprites can enter/exit smoothly.
        _track = _bands + 20
        self._spec_idle_phase = (self._spec_idle_phase + (0.35 * _spd)) % float(_track)

        _y0 = max(0, min(_levels - 5, (_levels // 2) - 2))
        _pac_x = int(self._spec_idle_phase) - 6
        _ghost_x = _pac_x + 10
        if _ghost_x > _bands + 5:
            _ghost_x -= _track

        _pac_closed = [
            "01110",
            "11111",
            "11111",
            "11111",
            "01110",
        ]
        _pac_open = [
            "01110",
            "11100",
            "11000",
            "11100",
            "01110",
        ]
        _ghost = [
            "01110",
            "11111",
            "10101",
            "11111",
            "10101",
        ]
        # Keep mouth cadence fixed so idle speed slider only affects chase speed.
        _pac = _pac_open if (int(time.monotonic() * 5.0) % 2) else _pac_closed

        def _set_px(_x, _y, _color):
            if 0 <= _x < _bands and 0 <= _y < _levels:
                self._spec_segments[_x][_y].bgcolor = _color

        def _draw_mask(_mask, _x0, _y0_local, _color):
            for _ry, _row in enumerate(_mask):
                for _rx, _bit in enumerate(_row):
                    if _bit == "1":
                        _set_px(_x0 + _rx, _y0_local + _ry, _color)

        try:
            for _x in range(_bands):
                for _y in range(_levels):
                    self._spec_segments[_x][_y].bgcolor = _bg

            _draw_mask(_pac, _pac_x, _y0, "#ffd400")
            _draw_mask(_ghost, _ghost_x, _y0, "#ff4d6d")

            # Ghost eyes
            _set_px(_ghost_x + 1, _y0 + 1, "#c8f7ff")
            _set_px(_ghost_x + 3, _y0 + 1, "#c8f7ff")
        except Exception:
            # Never allow an idle animation exception to stall rendering.
            self._render_spectrum_idle_aurora()
            return

        try:
            self._spectrum_box.update()
        except Exception:
            pass

    def _render_spectrum_idle_tetris(self):
        """Idle effect: classic Tetris-style playfield with falling tetromino."""
        if not self._spec_segments:
            return

        _bands = max(1, self._spec_bands)
        _levels = max(1, self._spec_levels)
        _spd = max(0.25, min(3.0, float(self._spec_idle_speed)))
        _bg = "#101010"

        self._spec_idle_phase = (self._spec_idle_phase + (0.85 * _spd)) % 100000.0
        _tick = int(self._spec_idle_phase)

        _well_w = max(6, min(10, _bands - 2))
        _well_h = _levels
        _left = max(0, (_bands - _well_w) // 2)
        _right = _left + _well_w - 1
        _wall_l = _left - 1
        _wall_r = _right + 1

        _pieces = [
            ([(0, 1), (1, 1), (2, 1), (3, 1)], "#4dd0e1"),
            ([(1, 0), (2, 0), (1, 1), (2, 1)], "#ffd54f"),
            ([(1, 0), (0, 1), (1, 1), (2, 1)], "#ba68c8"),
            ([(0, 0), (0, 1), (1, 1), (2, 1)], "#ff8a65"),
            ([(2, 0), (0, 1), (1, 1), (2, 1)], "#64b5f6"),
            ([(1, 0), (2, 0), (0, 1), (1, 1)], "#81c784"),
            ([(0, 0), (1, 0), (1, 1), (2, 1)], "#f06292"),
        ]

        def _set_px(_x, _y, _color):
            if 0 <= _x < _bands and 0 <= _y < _levels:
                self._spec_segments[_x][_y].bgcolor = _color

        def _draw_piece(_coords, _x0, _y0, _color):
            for _dx, _dy in _coords:
                _set_px(_x0 + _dx, _y0 + _dy, _color)

        try:
            for _x in range(_bands):
                for _y in range(_levels):
                    self._spec_segments[_x][_y].bgcolor = _bg

            # Draw the playfield well walls.
            for _y in range(_well_h):
                _set_px(_wall_l, _y, "#2f2f2f")
                _set_px(_wall_r, _y, "#2f2f2f")

            # Subtle well grid so blocks read as "cells".
            for _wx in range(_well_w):
                for _wy in range(_well_h):
                    if ((_wx + _wy) % 2) == 0:
                        _set_px(_left + _wx, _wy, "#121212")

            # Static-ish stack profile near bottom for a classic in-progress board feel.
            _stack_heights = []
            for _wx in range(_well_w):
                _h = 2 + int(((math.sin((_wx * 0.9) + (_tick * 0.08)) + 1.0) * 1.5))
                _stack_heights.append(max(1, min(_well_h - 5, _h)))

            _piece_cycle = _well_h + 7
            _piece_idx = (_tick // _piece_cycle) % len(_pieces)
            _piece_coords, _piece_color = _pieces[_piece_idx]
            _piece_x = ((_tick // _piece_cycle) * 3) % max(1, (_well_w - 4))
            _piece_y = -3 + (_tick % _piece_cycle)

            # Keep a vertical drop lane more open so the active piece is visible longer.
            for _dx, _ in _piece_coords:
                _col = _piece_x + _dx
                if 0 <= _col < _well_w:
                    _stack_heights[_col] = max(1, _stack_heights[_col] - 2)

            _stack_palette = ["#2aa198", "#d79921", "#6c71c4", "#859900", "#cb4b16", "#268bd2", "#d33682"]
            for _wx in range(_well_w):
                _h = _stack_heights[_wx]
                for _n in range(_h):
                    _yy = (_well_h - 1) - _n
                    _set_px(_left + _wx, _yy, _stack_palette[(_wx + _n + (_tick // 3)) % len(_stack_palette)])

            # Periodic fake line-clear flash for arcade flavor.
            if (_tick % 40) >= 34:
                _flash_y = _well_h - 1 - ((_tick // 2) % 2)
                for _wx in range(_well_w):
                    _set_px(_left + _wx, _flash_y, "#f0f0f0")

            _draw_piece(_piece_coords, _left + _piece_x, _piece_y, _piece_color)
        except Exception:
            self._render_spectrum_idle_aurora()
            return

        try:
            self._spectrum_box.update()
        except Exception:
            pass

    def _render_spectrum_idle_invaders(self):
        """Idle effect: space invader formation marching left and right."""
        if not self._spec_segments:
            return

        _bands = max(1, self._spec_bands)
        _levels = max(1, self._spec_levels)
        _spd = max(0.25, min(3.0, float(self._spec_idle_speed)))
        _bg = "#101010"

        self._spec_idle_phase = (self._spec_idle_phase + (0.45 * _spd)) % 100000.0
        _phase = self._spec_idle_phase

        _invader_a = [
            "00100100",
            "01111110",
            "11011011",
            "11111111",
            "01111110",
            "01000010",
        ]
        _invader_b = [
            "00100100",
            "01111110",
            "11011011",
            "11111111",
            "00111100",
            "01100110",
        ]

        def _set_px(_x, _y, _color):
            if 0 <= _x < _bands and 0 <= _y < _levels:
                self._spec_segments[_x][_y].bgcolor = _color

        def _draw_mask(_mask, _x0, _y0, _color):
            for _ry, _row in enumerate(_mask):
                for _rx, _bit in enumerate(_row):
                    if _bit == "1":
                        _set_px(_x0 + _rx, _y0 + _ry, _color)

        try:
            for _x in range(_bands):
                for _y in range(_levels):
                    self._spec_segments[_x][_y].bgcolor = _bg

            _frame = int(_phase)
            _wiggle = 1 if ((_frame // 2) % 2) else 0
            _mask = _invader_a if ((_frame // 3) % 2) else _invader_b

            _span = max(1, _bands - 26)
            _step = _frame % (2 * _span)
            _offset = _step if _step < _span else (2 * _span - _step)
            _x0 = max(0, min(_bands - 1, 1 + _offset))

            for _i in range(3):
                _draw_mask(_mask, _x0 + (_i * 9), 2 + _wiggle, "#8cff66")

            _laser_x = _x0 + 12
            _laser_top = 9 + (_frame % max(2, _levels - 9))
            for _y in range(_laser_top, min(_levels, _laser_top + 4)):
                _set_px(_laser_x, _y, "#ff5252")
        except Exception:
            self._render_spectrum_idle_aurora()
            return

        try:
            self._spectrum_box.update()
        except Exception:
            pass

    def _render_spectrum_idle_snake(self):
        """Idle effect: classic snake slithering through a serpentine path."""
        if not self._spec_segments:
            return

        _bands = max(1, self._spec_bands)
        _levels = max(1, self._spec_levels)
        _spd = max(0.25, min(3.0, float(self._spec_idle_speed)))
        _bg = "#101010"

        self._spec_idle_phase = (self._spec_idle_phase + (1.05 * _spd)) % 100000.0
        _phase = int(self._spec_idle_phase)

        _path = []
        for _y in range(_levels):
            if (_y % 2) == 0:
                for _x in range(_bands):
                    _path.append((_x, _y))
            else:
                for _x in range(_bands - 1, -1, -1):
                    _path.append((_x, _y))

        def _set_px(_x, _y, _color):
            if 0 <= _x < _bands and 0 <= _y < _levels:
                self._spec_segments[_x][_y].bgcolor = _color

        try:
            for _x in range(_bands):
                for _y in range(_levels):
                    self._spec_segments[_x][_y].bgcolor = _bg

            if not _path:
                return

            _head_idx = _phase % len(_path)
            _len_snake = max(8, min(len(_path) // 2, _bands + 6))
            for _i in range(_len_snake):
                _idx = (_head_idx - _i) % len(_path)
                _x, _y = _path[_idx]
                if _i == 0:
                    _c = "#d7ff8a"
                else:
                    _g = max(72, 255 - (_i * 9))
                    _c = f"#00{_g:02x}28"
                _set_px(_x, _y, _c)

            _food_idx = (_head_idx + (_bands * 2 + 5)) % len(_path)
            _fx, _fy = _path[_food_idx]
            _set_px(_fx, _fy, "#ff6a3d")
        except Exception:
            self._render_spectrum_idle_aurora()
            return

        try:
            self._spectrum_box.update()
        except Exception:
            pass

    def _build_starwars_tape(self, bands, levels):
        """Build vertical bitmap tape for Star Wars crawl.
        Returns (tape, tape_title), each a list[vrows] of list[bands] booleans.
        """
        _line_h = 9
        _font_h = 7
        _crawl = [
            ("", False),
            ("", False),
            ("STAR", True),
            ("WARS", True),
            ("", False),
            ("A LONG", False),
            ("TIME AGO", False),
            ("IN A", False),
            ("GALAXY", False),
            ("FAR FAR", False),
            ("AWAY...", False),
            ("", False),
            ("WLED", False),
            ("COMMAND", False),
            ("CENTER+", False),
            ("", False),
            ("A NEW", False),
            ("HOPE FOR", False),
            ("YOUR", False),
            ("SMART", False),
            ("LIGHTS", False),
            ("", False),
            ("", False),
            ("", False),
            ("", False),
            ("", False),
        ]

        _prefix = levels
        _total_vrows = _prefix + len(_crawl) * _line_h
        _tape = [[False] * bands for _ in range(_total_vrows)]
        _tape_title = [[False] * bands for _ in range(_total_vrows)]
        _vr_base = _prefix

        for _text, _is_title in _crawl:
            _text = _text.strip()
            if _text:
                _cols = self._build_spec_text_columns(_text)
                _tw = len(_cols)
                _x0 = max(0, (bands - _tw) // 2)
                for _cx, _cbits in enumerate(_cols):
                    _vx = _x0 + _cx
                    if _vx >= bands:
                        break
                    for _fy in range(min(_font_h, len(_cbits))):
                        if _cbits[_fy]:
                            _vr = _vr_base + _fy
                            if 0 <= _vr < _total_vrows:
                                _tape[_vr][_vx] = True
                                if _is_title:
                                    _tape_title[_vr][_vx] = True
            _vr_base += _line_h

        return _tape, _tape_title

    def _render_spectrum_idle_starwars(self):
        """Star Wars crawl using regular graphics controls (not the SA grid)."""
        _w = int(self._spectrum_box.width or self._spec_box_graphics_size[0])
        _h = int(self._spectrum_box.height or self._spec_box_graphics_size[1])
        _w = max(120, _w)
        _h = max(80, _h)

        self._ensure_spectrum_graphics_controls(_w, _h)

        _spd = max(0.25, min(3.0, float(self._spec_idle_speed)))
        _lines = [
            ("STAR WARS", True),
            ("IN A LAND FAR AWAY...", False),
            ("WLED COMMAND CENTER+", False),
            ("A NEW HOPE", False),
            ("FOR SMART LIGHT CONTROL", False),
            ("MAY YOUR LIGHTS", False),
            ("BE WITH YOU", False),
        ]

        _line_gap = 16
        _start_y = _h - 28
        _line_count = max(1, len(_lines))
        # Restart immediately after the last line exits the top cutoff (-80).
        _cycle_px = _start_y + ((_line_count - 1) * _line_gap) + 80
        self._spec_idle_phase = (self._spec_idle_phase + (0.30 * _spd)) % float(max(1, _cycle_px))
        _base_y = _start_y - self._spec_idle_phase

        _now = time.monotonic()
        for _i, _dot in enumerate(self._spec_graphics_stars):
            _tw = int(_now * 3.4 + (_i * 1.23)) % 8
            _alpha = (0.22, 0.35, 0.5, 0.7, 0.45, 0.3, 0.18, 0.08)[_tw]
            _v = (120, 145, 180, 220, 160, 140, 115, 90)[_tw]
            _dot.bgcolor = f"#{_v:02x}{_v:02x}{_v:02x}"
            _dot.opacity = _alpha

        for _idx, (_slot, _txt) in enumerate(self._spec_graphics_lines):
            if _idx >= len(_lines):
                _slot.visible = False
                continue

            _text, _is_title = _lines[_idx]
            _y = _base_y + (_idx * _line_gap)
            if (not _text) or _y < -80 or _y > (_h + 60):
                _slot.visible = False
                continue

            _depth = max(0.0, min(1.0, _y / max(1.0, float(_h))))
            _scale = 0.18 + ((_depth ** 1.18) * 1.30)
            _base_fs = 30 if _is_title else 22
            _font_size = max(8, int(_base_fs * _scale))

            # Weighted width estimate prevents clipping on wide glyphs (W, M, etc.).
            _char_units = 0.0
            for _ch in _text:
                if _ch == " ":
                    _char_units += 0.42
                elif _ch in "WM@#%&":
                    _char_units += 1.0
                elif _ch in "I|.,:;!'":
                    _char_units += 0.40
                else:
                    _char_units += 0.72

            _side_pad = max(14, int(_font_size * 0.95))
            _est_w = max(30, int((_char_units * _font_size) + (_side_pad * 2)))
            _est_h = max(14, int(_font_size * 1.75))

            _slot.left = int((_w - _est_w) / 2)
            _slot.top = int(_y)
            _slot.width = _est_w
            _slot.height = _est_h
            _slot.visible = True

            if _is_title:
                _r = 255
                _g = 140
                _b = 20
                _txt.weight = ft.FontWeight.BOLD
            else:
                _r = 255
                _g = 214
                _b = 80
                _txt.weight = ft.FontWeight.W_600

            _txt.value = _text
            _txt.size = _font_size
            _txt.color = f"#{_r:02x}{_g:02x}{_b:02x}"

        try:
            self._spectrum_box.update()
        except Exception:
            pass

    def _refresh_spectrum_sources(self):
        """Refresh available spectrum audio sources immediately."""
        try:
            import importlib
            _sc = importlib.import_module("soundcard")
            _all_mics = list(_sc.all_microphones(include_loopback=True))
            _raw_sources = [(m.name, idx) for idx, m in enumerate(_all_mics)]
            _rank = {n: i for i, n in enumerate(self._spec_source_order)}
            self._spec_audio_sources = sorted(_raw_sources, key=lambda it: (_rank.get(it[0], 10**9), it[1]))

            _new_order = []
            for _name, _ in self._spec_audio_sources:
                if _name not in _new_order:
                    _new_order.append(_name)
            self._spec_source_order = _new_order
            return True
        except Exception:
            self._spec_audio_sources = []
            return False

    def _spec_profile_key(self, source_name=None):
        _name = self._spec_selected_source if source_name is None else source_name
        return "__default__" if not _name else str(_name)

    def _save_spec_profile(self, source_name=None):
        _key = self._spec_profile_key(source_name)
        self._spec_profiles[_key] = {
            "sensitivity": float(self._spec_sensitivity),
            "reactivity": float(self._spec_reactivity),
            "bar_decay": float(self._spec_bar_decay),
            "peak_decay": float(self._spec_peak_decay),
            "eq_gains": [float(v) for v in self._spec_eq_gains],
        }

    def _load_spec_profile(self, source_name=None):
        _key = self._spec_profile_key(source_name)
        _p = self._spec_profiles.get(_key, {}) if isinstance(self._spec_profiles, dict) else {}

        def _clamp(v, lo, hi, default):
            try:
                return max(lo, min(hi, float(v)))
            except Exception:
                return default

        self._spec_sensitivity = _clamp(_p.get("sensitivity", 0.85), 0.1, 1.5, 0.85)
        self._spec_reactivity = _clamp(_p.get("reactivity", 3.0), 0.25, 3.0, 3.0)
        self._spec_bar_decay = _clamp(_p.get("bar_decay", 2.0), 0.1, 5.0, 2.0)
        self._spec_peak_decay = _clamp(_p.get("peak_decay", 1.0), 0.1, 5.0, 1.0)

        _eq = _p.get("eq_gains", None)
        if isinstance(_eq, list) and len(_eq) == len(self._spec_eq_freqs):
            try:
                self._spec_eq_gains = [max(0.25, min(3.0, float(v))) for v in _eq]
            except Exception:
                self._spec_eq_gains = [1.0] * len(self._spec_eq_freqs)
        else:
            self._spec_eq_gains = [1.0] * len(self._spec_eq_freqs)

    def _pick_default_spectrum_source(self, _sc):
        """Prefer loopback/output capture source; fall back to microphone only if needed."""
        try:
            _speaker = _sc.default_speaker()
        except Exception:
            _speaker = None

        try:
            _all_mics = list(_sc.all_microphones(include_loopback=True))
        except Exception:
            _all_mics = []

        # 1) Exact API path: loopback mic by default speaker id
        if _speaker is not None:
            try:
                _loop = _sc.get_microphone(id=_speaker.id, include_loopback=True)
                if _loop is not None:
                    return _loop, "output-loopback"
            except Exception:
                pass

        # 2) Name heuristics: pick loopback-like devices first
        _speaker_name = (_speaker.name.lower() if _speaker and getattr(_speaker, "name", None) else "")
        for _m in _all_mics:
            _n = str(getattr(_m, "name", "")).lower()
            if "loopback" in _n or "stereo mix" in _n:
                if _speaker_name and _speaker_name in _n:
                    return _m, "output-loopback"
        for _m in _all_mics:
            _n = str(getattr(_m, "name", "")).lower()
            if "loopback" in _n or "stereo mix" in _n:
                return _m, "output-loopback"

        # 3) Fallback input mic only as last resort
        try:
            _mic = _sc.default_microphone()
            if _mic is not None:
                return _mic, "input-microphone"
        except Exception:
            pass

        return None, None

    def _open_spectrum_source_selector(self, _=None):
        try:
            self._show_spectrum_source_selector()
        except Exception as ex:
            self.log(f"[Spectrum] Source selector failed: {ex}", color="orange400")

    def _open_spectrum_idle_settings(self, _=None):
        try:
            self._show_spectrum_idle_settings()
        except Exception as ex:
            self.log(f"[Spectrum] Idle settings failed: {ex}", color="orange400")

    def _show_spectrum_idle_settings(self):
        """Show idle-effects + source controls in a dedicated dialog."""
        self.log("[Spectrum] Idle settings opened", color="grey500")
        self._refresh_spectrum_sources()

        _idle_timeout_txt = ft.Text(f"{int(self._spec_idle_timeout)}s", size=12, color="#ff9800")
        _idle_speed_txt = ft.Text(f"{self._spec_idle_speed:.2f}x", size=12, color="#ff9800")

        _idle_options = [
            ("aurora", "Ambient Wave"),
            ("pulse", "Pulse Field"),
            ("text", "Marquee Text"),
            ("rainbow", "Rainbow Wave"),
            ("pacman", "Pac-Man Chase"),
            ("tetris", "Tetris Stack"),
            ("invaders", "Space Invaders"),
            ("snake", "Snake Crawl"),
            ("starwars", "Star Wars Crawl"),
        ]

        def _ensure_idle_cycle_default():
            if not isinstance(self._spec_idle_cycle_effects, list):
                self._spec_idle_cycle_effects = [k for k, _ in _idle_options]
            self._spec_idle_cycle_effects = [k for k in self._spec_idle_cycle_effects if any(k == o[0] for o in _idle_options)]
            if not self._spec_idle_cycle_effects:
                self._spec_idle_cycle_effects = [k for k, _ in _idle_options]

        _ensure_idle_cycle_default()

        def on_idle_timeout_change(e):
            self._spec_idle_timeout = round(float(e.control.value), 1)
            _idle_timeout_txt.value = f"{int(round(self._spec_idle_timeout))}s"
            _idle_timeout_txt.update()

        def on_idle_effect_change(e):
            _fx = str(e.control.value or "random").lower()
            self._spec_idle_effect = _fx if _fx in ("random", "aurora", "pulse", "text", "rainbow", "pacman", "tetris", "invaders", "snake", "starwars") else "random"

        def on_idle_speed_change(e):
            self._spec_idle_speed = round(float(e.control.value), 2)
            _idle_speed_txt.value = f"{self._spec_idle_speed:.2f}x"
            _idle_speed_txt.update()

        def on_cycle_fx_toggle(fx_key, enabled):
            _ensure_idle_cycle_default()
            if enabled:
                if fx_key not in self._spec_idle_cycle_effects:
                    self._spec_idle_cycle_effects.append(fx_key)
            else:
                self._spec_idle_cycle_effects = [x for x in self._spec_idle_cycle_effects if x != fx_key]
                if not self._spec_idle_cycle_effects:
                    # Keep at least one effect active.
                    self._spec_idle_cycle_effects = [fx_key]

        source_list = None

        def on_source_selected(source_name):
            self._save_spec_profile()
            self._spec_selected_source = source_name if source_name != "Default" else None
            if self._spec_selected_source:
                self._spec_source_order = [self._spec_selected_source] + [n for n in self._spec_source_order if n != self._spec_selected_source]
            self._load_spec_profile(self._spec_selected_source)
            self._spec_source_changed = True
            if self._spec_disabled:
                self._spec_disabled = False
                threading.Thread(target=self._audio_analyzer_loop, daemon=True).start()
            self._refresh_spectrum_sources()
            if source_list is not None:
                source_list.controls = _build_source_buttons()
                source_list.update()

        def _build_source_buttons():
            if self._spec_audio_sources:
                _source_buttons = []
                if self._spec_selected_source:
                    _source_buttons.append(ft.TextButton(self._spec_selected_source, on_click=lambda _, n=self._spec_selected_source: on_source_selected(n), style=ft.ButtonStyle(color="#ff9800")))
                    _source_buttons.append(ft.TextButton("Default", on_click=lambda _: on_source_selected("Default"), style=ft.ButtonStyle(color="grey500")))
                    for name, _idx in self._spec_audio_sources:
                        if name == self._spec_selected_source:
                            continue
                        _source_buttons.append(ft.TextButton(name, on_click=lambda _, n=name: on_source_selected(n), style=ft.ButtonStyle(color="grey500")))
                else:
                    _source_buttons.append(ft.TextButton("Default", on_click=lambda _: on_source_selected("Default"), style=ft.ButtonStyle(color="#ff9800")))
                    for name, _idx in self._spec_audio_sources:
                        _source_buttons.append(ft.TextButton(name, on_click=lambda _, n=name: on_source_selected(n), style=ft.ButtonStyle(color="grey500")))
                return _source_buttons
            return [
                ft.Text("No compatible sources detected.", size=12, color="orange400"),
                ft.Text("Tip: Enable Stereo Mix or play audio, then reopen this panel.", size=11, color="grey500"),
            ]

        _idle_effect_dd = ft.Dropdown(
            width=180,
            value=self._spec_idle_effect,
            options=[
                ft.dropdown.Option("random", "Random Cycle"),
                ft.dropdown.Option("aurora", "Ambient Wave"),
                ft.dropdown.Option("pulse", "Pulse Field"),
                ft.dropdown.Option("text", "Marquee Text"),
                ft.dropdown.Option("rainbow", "Rainbow Wave"),
                ft.dropdown.Option("pacman", "Pac-Man Chase"),
                ft.dropdown.Option("tetris", "Tetris Stack"),
                ft.dropdown.Option("invaders", "Space Invaders"),
                ft.dropdown.Option("snake", "Snake Crawl"),
                ft.dropdown.Option("starwars", "Star Wars Crawl"),
            ],
            on_change=on_idle_effect_change,
            text_size=12,
            dense=True,
        )

        _cycle_checks = []
        for _fx_key, _fx_label in _idle_options:
            _cycle_checks.append(
                ft.Checkbox(
                    label=_fx_label,
                    value=(_fx_key in self._spec_idle_cycle_effects),
                    on_change=lambda e, k=_fx_key: on_cycle_fx_toggle(k, bool(e.control.value)),
                    active_color="#ff9800",
                )
            )

        _left_col_checks = [c for i, c in enumerate(_cycle_checks) if (i % 2) == 0]
        _right_col_checks = [c for i, c in enumerate(_cycle_checks) if (i % 2) == 1]

        _cycle_grid = ft.Row([
            ft.Column(_left_col_checks, spacing=0, tight=True, expand=True),
            ft.Column(_right_col_checks, spacing=0, tight=True, expand=True),
        ], spacing=10, expand=True)

        dlg = ft.AlertDialog(
            title=ft.Text("Idle Effects Settings"),
            content=ft.Column(
                [
                    ft.Row([
                        ft.Container(content=_cycle_grid, expand=True),
                        ft.Container(content=_idle_effect_dd, width=190, alignment=ft.alignment.top_right),
                    ], spacing=8, vertical_alignment=ft.CrossAxisAlignment.START),
                    ft.Row([
                        ft.Text("Timeout:", size=12, color="grey400", width=62),
                        _idle_timeout_txt,
                        ft.Slider(min=2.0, max=30.0, value=self._spec_idle_timeout, divisions=28, active_color="#ff9800", on_change=on_idle_timeout_change, expand=True),
                    ], spacing=8, vertical_alignment=ft.CrossAxisAlignment.CENTER),
                    ft.Row([
                        ft.Text("Idle Speed:", size=12, color="grey400", width=62),
                        _idle_speed_txt,
                        ft.Slider(min=0.25, max=3.0, value=self._spec_idle_speed, divisions=55, active_color="#ff9800", on_change=on_idle_speed_change, expand=True),
                    ], spacing=8, vertical_alignment=ft.CrossAxisAlignment.CENTER),
                    ft.Divider(height=1, color="grey800"),
                    ft.Text("Sound Sources:", size=12, color="grey400"),
                    (source_list := ft.Column(_build_source_buttons(), scroll="auto", tight=True, height=120)),
                ],
                tight=True,
                scroll=ft.ScrollMode.AUTO,
                width=430,
                height=500,
            ),
            actions=[
                ft.TextButton("Close", on_click=lambda _: self.page.close(dlg)),
                ft.ElevatedButton("Save", on_click=lambda _: (self.save_cache(), self.page.close(dlg)), bgcolor="#1a1a2e", color="white"),
            ],
        )
        try:
            self.page.open(dlg)
        except Exception:
            self.page.dialog = dlg
            dlg.open = True
            self.page.update()

    def _show_spectrum_source_selector(self):
        """Show a dialog to select the audio source and sensitivity for spectrum analyzer."""
        self.log("[Spectrum] Source selector opened", color="grey500")
        self._refresh_spectrum_sources()

        # Dialog runs in preview mode. Changes apply live, but are not written
        # to JSON unless Save is clicked.
        _spec_saved = False
        if not self._spec_preview_pending:
            self._spec_preview_snapshot = {
                "selected_source": self._spec_selected_source,
                "source_order": list(self._spec_source_order),
                "profiles": json.loads(json.dumps(self._spec_profiles if isinstance(self._spec_profiles, dict) else {})),
                "target_fps": int(self._spec_target_fps),
                "analysis_bands": int(self._spec_analysis_bands),
                "sensitivity": float(self._spec_sensitivity),
                "reactivity": float(self._spec_reactivity),
                "bar_decay": float(self._spec_bar_decay),
                "peak_decay": float(self._spec_peak_decay),
                "sample_rate": int(self._spec_sample_rate),
                "sampling_enabled": bool(self._spec_sampling_enabled),
                "mode": str(self._spec_mode),
                "idle_enabled": bool(self._spec_idle_enabled),
                "idle_timeout": float(self._spec_idle_timeout),
                "idle_effect": str(self._spec_idle_effect),
                "idle_speed": float(self._spec_idle_speed),
                "idle_cycle_effects": list(self._spec_idle_cycle_effects),
                "eq_gains": [float(v) for v in self._spec_eq_gains],
            }
            self._spec_preview_pending = True

        def _restore_preview_snapshot():
            _snap = self._spec_preview_snapshot if isinstance(self._spec_preview_snapshot, dict) else None
            if not _snap:
                return
            _current_selected = self._spec_selected_source
            self._spec_selected_source = _snap.get("selected_source", None)
            self._spec_source_order = list(_snap.get("source_order", []))
            self._spec_profiles = json.loads(json.dumps(_snap.get("profiles", {})))
            _prev_analysis_bands = int(getattr(self, "_spec_analysis_bands", self._spec_bands) or self._spec_bands)
            try:
                self._spec_target_fps = max(8, min(30, int(round(float(_snap.get("target_fps", 25))))))
            except Exception:
                self._spec_target_fps = 25
            self._set_spec_analysis_bands(_snap.get("analysis_bands", self._spec_bands), restart_audio=False, reset_now=False)
            self._spec_sensitivity = float(_snap.get("sensitivity", 0.85))
            self._spec_reactivity = float(_snap.get("reactivity", 3.0))
            self._spec_bar_decay = float(_snap.get("bar_decay", 2.0))
            self._spec_peak_decay = float(_snap.get("peak_decay", 1.0))
            _prev_sr = int(getattr(self, "_spec_sample_rate", 48000) or 48000)
            _prev_sampling = bool(getattr(self, "_spec_sampling_enabled", True))
            try:
                _sr = int(_snap.get("sample_rate", 48000))
            except Exception:
                _sr = 48000
            self._spec_sample_rate = _sr if _sr in (16000, 22050, 32000, 44100, 48000) else 48000
            self._spec_sampling_enabled = bool(_snap.get("sampling_enabled", True))
            _mode = str(_snap.get("mode", "classic")).lower()
            self._spec_mode = _mode if _mode in ("classic", "vu", "random", "random_song") else "classic"
            if self._spec_mode in ("random", "random_song"):
                self._advance_spectrum_random_mode()
                self._spec_mode_random_next_ts = time.monotonic() + max(1.0, float(self._spec_mode_random_cycle_seconds))
                self._spec_mode_song_switch_armed = True
            self._spec_idle_enabled = bool(_snap.get("idle_enabled", True))
            self._spec_idle_timeout = float(_snap.get("idle_timeout", 2.0))
            _idle_fx = str(_snap.get("idle_effect", "random")).lower()
            self._spec_idle_effect = _idle_fx if _idle_fx in ("random", "aurora", "pulse", "text", "rainbow", "pacman", "tetris", "invaders", "snake", "starwars") else "random"
            try:
                self._spec_idle_speed = max(0.25, min(3.0, float(_snap.get("idle_speed", 3.0))))
            except Exception:
                self._spec_idle_speed = 3.0
            _idle_cycle = _snap.get("idle_cycle_effects", self._spec_idle_cycle_effects)
            if isinstance(_idle_cycle, list):
                _allowed = ["aurora", "pulse", "text", "rainbow", "pacman", "tetris", "invaders", "snake", "starwars"]
                self._spec_idle_cycle_effects = [x for x in _idle_cycle if isinstance(x, str) and x in _allowed]
                if not self._spec_idle_cycle_effects:
                    self._spec_idle_cycle_effects = list(_allowed)
            self._spec_eq_gains = [float(v) for v in _snap.get("eq_gains", [1.0] * len(self._spec_eq_freqs))]
            if (_current_selected != self._spec_selected_source) or (_prev_sr != self._spec_sample_rate) or (_prev_sampling != self._spec_sampling_enabled) or (_prev_analysis_bands != int(self._spec_analysis_bands)):
                self._spec_source_changed = True
                if self._spec_disabled:
                    self._spec_disabled = False
                    threading.Thread(target=self._audio_analyzer_loop, daemon=True).start()
            self._sync_spec_quick_buttons()

        def _revert_preview_and_close(_=None):
            nonlocal _spec_saved
            if not _spec_saved:
                _restore_preview_snapshot()
                self._spec_preview_pending = False
                self._spec_preview_snapshot = None
                self.log("[Spectrum] Preview changes discarded", color="grey500")
            self.page.close(dlg)

        def _close_keep_preview(_=None):
            # Close behaves like click-away: keep temporary preview state.
            if (not _spec_saved) and self._spec_preview_pending:
                self.log("[Spectrum] Preview kept (not saved)", color="grey500")
            self.page.close(dlg)

        def _save_and_close(_=None):
            nonlocal _spec_saved
            self._save_spec_profile()
            self.save_cache()
            _spec_saved = True
            self._spec_preview_pending = False
            self._spec_preview_snapshot = None
            self.log("[Spectrum] Settings saved", color="green400")
            self.page.close(dlg)

        def _dismiss_keep_preview(_=None):
            # Click-away dismiss keeps temporary preview changes active.
            if (not _spec_saved) and self._spec_preview_pending:
                self.log("[Spectrum] Preview kept (not saved)", color="grey500")

        source_list = None
        _sens_slider = None
        _react_slider = None
        _bar_decay_slider = None
        _peak_decay_slider = None

        def on_source_selected(source_name):
            nonlocal _active_eq_preset
            # Persist current source profile before switching.
            self._save_spec_profile()

            self._spec_selected_source = source_name if source_name != "Default" else None

            # Move selected source to top while preserving relative order of others.
            if self._spec_selected_source:
                self._spec_source_order = [self._spec_selected_source] + [
                    n for n in self._spec_source_order if n != self._spec_selected_source
                ]

            # Load profile for the newly selected source/default.
            self._load_spec_profile(self._spec_selected_source)

            self._spec_source_changed = True
            if self._spec_disabled:
                self._spec_disabled = False
                threading.Thread(target=self._audio_analyzer_loop, daemon=True).start()

            # Refresh ordered source list and keep dialog open.
            self._refresh_spectrum_sources()
            if source_list is not None:
                source_list.controls = _build_source_buttons()
                source_list.update()

            # Reflect loaded profile values in controls.
            if _sens_slider is not None:
                _sens_slider.value = max(_sens_slider.min, min(_sens_slider.max, float(self._spec_sensitivity)))
                _sens_slider.update()
            _sens_pct.value = f"{int(self._spec_sensitivity * 100)}%"
            _sens_pct.update()
            if _react_slider is not None:
                _react_slider.value = max(_react_slider.min, min(_react_slider.max, float(self._spec_reactivity)))
                _react_slider.update()
            _react_pct.value = f"{self._spec_reactivity:.2f}x"
            _react_pct.update()
            if _bar_decay_slider is not None:
                _bar_decay_slider.value = max(_bar_decay_slider.min, min(_bar_decay_slider.max, float(self._spec_bar_decay)))
                _bar_decay_slider.update()
            _bar_decay_pct.value = f"{self._spec_bar_decay:.2f}x"
            _bar_decay_pct.update()
            if _peak_decay_slider is not None:
                _peak_decay_slider.value = max(_peak_decay_slider.min, min(_peak_decay_slider.max, float(self._spec_peak_decay)))
                _peak_decay_slider.update()
            _peak_decay_pct.value = f"{self._spec_peak_decay:.2f}x"
            _peak_decay_pct.update()
            for i, s in enumerate(_eq_sliders):
                s.value = max(s.min, min(s.max, float(self._spec_eq_gains[i])))
                s.update()
                _eq_value_texts[i].value = f"{self._spec_eq_gains[i]:.2f}x"
                _eq_value_texts[i].update()
            _active_eq_preset = _detect_eq_preset_name()
            _refresh_eq_preset_buttons()

            self.log(f"[Spectrum] Switched to: {source_name}", color="grey500")

        def _build_source_buttons():
            # Create list of source buttons (always open dialog even if empty)
            if self._spec_audio_sources:
                _source_buttons = []

                if self._spec_selected_source:
                    _source_buttons.append(
                        ft.TextButton(
                            self._spec_selected_source,
                            on_click=lambda _, n=self._spec_selected_source: on_source_selected(n),
                            style=ft.ButtonStyle(color="#ff9800"),
                        )
                    )
                    _source_buttons.append(
                        ft.TextButton(
                            "Default",
                            on_click=lambda _: on_source_selected("Default"),
                            style=ft.ButtonStyle(color="grey500"),
                        )
                    )

                    for name, idx in self._spec_audio_sources:
                        if name == self._spec_selected_source:
                            continue
                        _source_buttons.append(
                            ft.TextButton(
                                name,
                                on_click=lambda _, n=name: on_source_selected(n),
                                style=ft.ButtonStyle(color="grey500"),
                            )
                        )
                else:
                    _source_buttons.append(
                        ft.TextButton(
                            "Default",
                            on_click=lambda _: on_source_selected("Default"),
                            style=ft.ButtonStyle(color="#ff9800"),
                        )
                    )

                    for name, idx in self._spec_audio_sources:
                        _source_buttons.append(
                            ft.TextButton(
                                name,
                                on_click=lambda _, n=name: on_source_selected(n),
                                style=ft.ButtonStyle(color="grey500"),
                            )
                        )
                return _source_buttons

            return [
                ft.Text("No compatible sources detected.", size=12, color="orange400"),
                ft.Text("Tip: Enable Stereo Mix or play audio, then reopen this panel.", size=11, color="grey500"),
            ]

        _sens_pct = ft.Text(f"{int(self._spec_sensitivity * 100)}%", size=12, color="#ff9800")
        _fps_txt = ft.Text(f"{int(self._spec_target_fps)} FPS", size=12, color="#ff9800")
        _bars_txt = ft.Text(f"{int(self._spec_analysis_bands)}", size=12, color="#ff9800")
        _react_pct = ft.Text(f"{self._spec_reactivity:.2f}x", size=12, color="#ff9800")
        _bar_decay_pct = ft.Text(f"{self._spec_bar_decay:.2f}x", size=12, color="#ff9800")
        _peak_decay_pct = ft.Text(f"{self._spec_peak_decay:.2f}x", size=12, color="#ff9800")
        _idle_timeout_txt = ft.Text(f"{int(self._spec_idle_timeout)}s", size=12, color="#ff9800")
        _idle_speed_txt = ft.Text(f"{self._spec_idle_speed:.2f}x", size=12, color="#ff9800")

        def on_target_fps_change(e):
            self._spec_target_fps = max(8, min(30, int(round(float(e.control.value)))))
            _fps_txt.value = f"{int(self._spec_target_fps)} FPS"
            _fps_txt.update()

        def on_analysis_bars_change(e):
            _new_bars = max(6, min(int(self._spec_bands), int(round(float(e.control.value)))))
            _bars_txt.value = f"{_new_bars}"
            _bars_txt.update()
            self._set_spec_analysis_bands(_new_bars, restart_audio=True, reset_now=False)

        def on_sensitivity_change(e):
            self._spec_sensitivity = round(float(e.control.value), 2)
            _sens_pct.value = f"{int(self._spec_sensitivity * 100)}%"
            _sens_pct.update()
            self._save_spec_profile()

        def on_reactivity_change(e):
            self._spec_reactivity = round(float(e.control.value), 2)
            _react_pct.value = f"{self._spec_reactivity:.2f}x"
            _react_pct.update()
            self._save_spec_profile()

        def on_bar_decay_change(e):
            self._spec_bar_decay = round(float(e.control.value), 2)
            _bar_decay_pct.value = f"{self._spec_bar_decay:.2f}x"
            _bar_decay_pct.update()
            self._save_spec_profile()

        def on_peak_decay_change(e):
            self._spec_peak_decay = round(float(e.control.value), 2)
            _peak_decay_pct.value = f"{self._spec_peak_decay:.2f}x"
            _peak_decay_pct.update()
            self._save_spec_profile()

        def on_mode_change(e):
            _mode = str(e.control.value or "classic").lower()
            self._spec_mode = _mode if _mode in ("classic", "vu", "random", "random_song") else "classic"
            if self._spec_mode in ("random", "random_song"):
                self._advance_spectrum_random_mode()
                self._spec_mode_random_next_ts = time.monotonic() + max(1.0, float(self._spec_mode_random_cycle_seconds))
                self._spec_mode_song_switch_armed = True

        def on_idle_enabled_change(e):
            self._spec_idle_enabled = bool(e.control.value)
            self._sync_spec_quick_buttons()

        def on_idle_timeout_change(e):
            self._spec_idle_timeout = round(float(e.control.value), 1)
            _idle_timeout_txt.value = f"{int(round(self._spec_idle_timeout))}s"
            _idle_timeout_txt.update()

        def on_idle_effect_change(e):
            _fx = str(e.control.value or "random").lower()
            self._spec_idle_effect = _fx if _fx in ("random", "aurora", "pulse", "text", "rainbow", "pacman", "tetris", "invaders", "snake", "starwars") else "random"

        def on_idle_speed_change(e):
            self._spec_idle_speed = round(float(e.control.value), 2)
            _idle_speed_txt.value = f"{self._spec_idle_speed:.2f}x"
            _idle_speed_txt.update()

        def on_sample_rate_change(e):
            _raw = str(e.control.value or "48000")
            try:
                _new_sr = int(_raw)
            except Exception:
                _new_sr = 48000
            if _new_sr not in (16000, 22050, 32000, 44100, 48000):
                _new_sr = 48000
            if _new_sr != int(getattr(self, "_spec_sample_rate", 48000) or 48000):
                self._spec_sample_rate = _new_sr
                self._spec_source_changed = True
                if self._spec_disabled:
                    self._spec_disabled = False
                    threading.Thread(target=self._audio_analyzer_loop, daemon=True).start()
                self.log(f"[Spectrum] Sample rate set to {self._spec_sample_rate} Hz", color="grey500")

        _sens_slider = ft.Slider(
            min=0.1, max=1.5,
            value=self._spec_sensitivity,
            divisions=28,
            active_color="#ff9800",
            on_change=on_sensitivity_change,
        )

        _mode_dd = ft.Dropdown(
            width=170,
            value=self._spec_mode,
            options=[
                ft.dropdown.Option("classic", "Classic"),
                ft.dropdown.Option("vu", "VU (L/R)"),
                ft.dropdown.Option("random", "Random (1 min)"),
                ft.dropdown.Option("random_song", "Random (Per Song)"),
            ],
            on_change=on_mode_change,
            text_size=12,
            dense=True,
        )

        sensitivity_section = ft.Column([
            ft.Row([ft.Text("FPS:", size=12, color="grey400"), _fps_txt], spacing=8),
            ft.Slider(
                min=8, max=30,
                value=float(self._spec_target_fps),
                divisions=22,
                active_color="#ff9800",
                on_change=on_target_fps_change,
            ),
            ft.Row([ft.Text("Bars:", size=12, color="grey400"), _bars_txt], spacing=8),
            ft.Slider(
                min=6, max=float(self._spec_bands),
                value=float(self._spec_analysis_bands),
                divisions=max(1, int(self._spec_bands) - 6),
                active_color="#ff9800",
                on_change=on_analysis_bars_change,
            ),
            ft.Text("Visual width stays the same; fewer analysis bars are stretched across the same display.", size=10, color="grey500"),
            ft.Divider(height=1, color="grey800"),
            ft.Row([ft.Text("Sensitivity:", size=12, color="grey400"), _sens_pct], spacing=8),
            _sens_slider,
            ft.Row([ft.Text("Reactivity:", size=12, color="grey400"), _react_pct], spacing=8),
            (_react_slider := ft.Slider(
                min=0.25, max=3.0,
                value=self._spec_reactivity,
                divisions=55,
                active_color="#ff9800",
                on_change=on_reactivity_change,
            )),
            ft.Row([ft.Text("Bar Decay:", size=12, color="grey400"), _bar_decay_pct], spacing=8),
            (_bar_decay_slider := ft.Slider(
                min=0.1, max=5.0,
                value=self._spec_bar_decay,
                divisions=49,
                active_color="#ff9800",
                on_change=on_bar_decay_change,
            )),
            ft.Row([ft.Text("Peak Decay:", size=12, color="grey400"), _peak_decay_pct], spacing=8),
            (_peak_decay_slider := ft.Slider(
                min=0.1, max=5.0,
                value=self._spec_peak_decay,
                divisions=49,
                active_color="#ff9800",
                on_change=on_peak_decay_change,
            )),
            ft.Row([
                ft.Text("Mode:", size=12, color="grey400"),
                ft.Container(content=_mode_dd, expand=True, alignment=ft.alignment.center_right),
            ], spacing=8, vertical_alignment=ft.CrossAxisAlignment.CENTER),
            ft.Divider(height=1, color="grey800"),
        ], spacing=0, tight=True)

        _eq_labels = ["60Hz", "170Hz", "310Hz", "600Hz", "1k", "3k", "6k", "12k", "14k", "15k"]
        _eq_value_texts = []
        _eq_sliders = []
        _eq_preset_btns = {}

        _eq_presets = {
            "Flat":  [1.00, 1.00, 1.00, 1.00, 1.00, 1.00, 1.00, 1.00, 1.00, 1.00],
            "Bass+": [2.20, 1.90, 1.50, 1.25, 1.05, 0.95, 0.90, 0.88, 0.88, 0.88],
            "Smile": [1.70, 1.45, 1.15, 0.95, 0.85, 1.00, 1.20, 1.35, 1.40, 1.40],
            "Vocal": [0.85, 0.90, 0.95, 1.10, 1.25, 1.35, 1.15, 0.95, 0.90, 0.90],
        }

        def _detect_eq_preset_name():
            _cur = [round(float(v), 2) for v in self._spec_eq_gains]
            for _name, _vals in _eq_presets.items():
                if _cur == [round(float(x), 2) for x in _vals]:
                    return _name
            return None

        _active_eq_preset = _detect_eq_preset_name()

        def _refresh_eq_preset_buttons():
            for _name, _btn in _eq_preset_btns.items():
                _color = "#ff9800" if _name == _active_eq_preset else "grey400"
                _btn.style = ft.ButtonStyle(color=_color, padding=ft.padding.symmetric(horizontal=6, vertical=2))
                try:
                    _btn.update()
                except Exception:
                    pass

        def _apply_eq_preset(preset_name):
            nonlocal _active_eq_preset
            self._spec_eq_gains = list(_eq_presets.get(preset_name, _eq_presets["Flat"]))
            for i, s in enumerate(_eq_sliders):
                s.value = self._spec_eq_gains[i]
                _eq_value_texts[i].value = f"{self._spec_eq_gains[i]:.2f}x"
                _eq_value_texts[i].update()
                s.update()
            _active_eq_preset = preset_name if preset_name in _eq_presets else None
            _refresh_eq_preset_buttons()
            self._save_spec_profile()

        def _on_eq_change(idx, e):
            nonlocal _active_eq_preset
            v = round(float(e.control.value), 2)
            self._spec_eq_gains[idx] = v
            _eq_value_texts[idx].value = f"{v:.2f}x"
            _eq_value_texts[idx].update()
            _active_eq_preset = _detect_eq_preset_name()
            _refresh_eq_preset_buttons()
            self._save_spec_profile()

        _eq_rows = []
        for i, lbl in enumerate(_eq_labels):
            _txt = ft.Text(f"{self._spec_eq_gains[i]:.2f}x", size=11, color="#ff9800", width=42)
            _eq_value_texts.append(_txt)
            _s = ft.Slider(
                min=0.25, max=3.0,
                value=float(self._spec_eq_gains[i]),
                divisions=55,
                active_color="#ff9800",
                on_change=lambda e, _i=i: _on_eq_change(_i, e),
                expand=True,
            )
            _eq_sliders.append(_s)
            _eq_rows.append(
                ft.Row([
                    ft.Text(lbl, size=11, color="grey400", width=38),
                    _s,
                    _txt,
                ], spacing=6)
            )

        _eq_btn_flat = ft.TextButton("Flat", on_click=lambda _: _apply_eq_preset("Flat"), style=ft.ButtonStyle(color="grey400", padding=ft.padding.symmetric(horizontal=6, vertical=2)))
        _eq_btn_bass = ft.TextButton("Bass+", on_click=lambda _: _apply_eq_preset("Bass+"), style=ft.ButtonStyle(color="grey400", padding=ft.padding.symmetric(horizontal=6, vertical=2)))
        _eq_btn_smile = ft.TextButton("Smile", on_click=lambda _: _apply_eq_preset("Smile"), style=ft.ButtonStyle(color="grey400", padding=ft.padding.symmetric(horizontal=6, vertical=2)))
        _eq_btn_vocal = ft.TextButton("Vocal", on_click=lambda _: _apply_eq_preset("Vocal"), style=ft.ButtonStyle(color="grey400", padding=ft.padding.symmetric(horizontal=6, vertical=2)))
        _eq_preset_btns.update({
            "Flat": _eq_btn_flat,
            "Bass+": _eq_btn_bass,
            "Smile": _eq_btn_smile,
            "Vocal": _eq_btn_vocal,
        })
        _refresh_eq_preset_buttons()

        eq_section = ft.Column([
            ft.Row([
                ft.Text("Visual EQ (UI only):", size=12, color="grey400"),
                _eq_btn_flat,
                _eq_btn_bass,
                _eq_btn_smile,
                _eq_btn_vocal,
            ], spacing=2, wrap=True),
            ft.Column(_eq_rows, spacing=0, tight=True),
            ft.Divider(height=1, color="grey800"),
        ], spacing=2, tight=True)

        dlg = ft.AlertDialog(
            title=ft.Text("Spectrum Analyzer Settings"),
            on_dismiss=_dismiss_keep_preview,
            content=ft.Column(
                [
                    sensitivity_section,
                    eq_section,
                ],
                tight=True,
                scroll=ft.ScrollMode.AUTO,
                width=430,
                height=460,
            ),
            actions=[
                ft.TextButton("Undo", on_click=lambda _: (_revert_preview_and_close(), self._show_spectrum_source_selector())),
                ft.TextButton("Close", on_click=_close_keep_preview),
                ft.ElevatedButton("Save", on_click=_save_and_close, bgcolor="#1a1a2e", color="white"),
            ],
        )
        try:
            self.page.open(dlg)
        except Exception:
            self.page.dialog = dlg
            dlg.open = True
            self.page.update()

    def _audio_analyzer_loop(self):
        """Capture loopback audio and drive the header spectrum analyzer."""
        time.sleep(1.0)
        _current_device = None
        _last_idle_only_render = 0.0

        while self.running and not self._spec_disabled:
            if not bool(getattr(self, "_spec_sampling_enabled", True)):
                _now = time.monotonic()
                _render_interval = self._get_spec_render_interval()
                self._spec_idle_active = bool(getattr(self, "_spec_idle_enabled", True))
                if self._spec_idle_active:
                    if _now - _last_idle_only_render >= _render_interval:
                        self._render_spectrum()
                        _last_idle_only_render = _now
                    self._spec_display_cleared = False
                else:
                    if not self._spec_display_cleared:
                        self._clear_spectrum_display()
                        self._spec_display_cleared = True
                time.sleep(_render_interval)
                continue
            else:
                self._spec_display_cleared = False

            try:
                import importlib
                _np = importlib.import_module("numpy")
                if not self._spec_np_patch_applied and hasattr(_np, "frombuffer") and hasattr(_np, "fromstring"):
                    _orig_fromstring = _np.fromstring

                    def _compat_fromstring(string, dtype=float, count=-1, sep=''):
                        # Route binary/buffer inputs to frombuffer to avoid NumPy fromstring warnings.
                        if sep == '' and not isinstance(string, str):
                            try:
                                return _np.frombuffer(memoryview(string), dtype=dtype, count=count)
                            except Exception:
                                pass
                        return _orig_fromstring(string, dtype=dtype, count=count, sep=sep)

                    _np.fromstring = _compat_fromstring
                    self._spec_np_patch_applied = True
                _sc = importlib.import_module("soundcard")
            except Exception:
                if not self._spec_log_once:
                    self._spec_log_once = True
                    self.log("[Spectrum] Install 'numpy' and 'soundcard' for live PC audio analyzer", color="grey500")
                time.sleep(2.0)
                continue

            try:
                # Enumerate audio sources once, at startup
                if not self._spec_audio_sources:
                    try:
                        self._refresh_spectrum_sources()
                        if self._spec_audio_sources:
                            self.log(f"[Spectrum] Found {len(self._spec_audio_sources)} audio source(s)", color="grey500")
                    except Exception:
                        # Fallback if enumerate fails
                        self._spec_audio_sources = []

                # Check if user selected a different source
                if self._spec_source_changed or _current_device is None:
                    _source_switch = self._spec_source_changed
                    self._spec_source_changed = False
                    self._spec_capture_channels = 2
                    # Force fresh resolution on switch/start so source changes take effect immediately.
                    _current_device = None
                    if self._spec_selected_source and self._spec_audio_sources:
                        # Find device by name
                        for name, idx in self._spec_audio_sources:
                            if name == self._spec_selected_source:
                                try:
                                    all_mics = list(_sc.all_microphones(include_loopback=True))
                                    if idx < len(all_mics):
                                        _current_device = all_mics[idx]
                                        self.log(f"[Spectrum] Using source: {self._spec_selected_source}", color="grey500")
                                        break
                                except Exception:
                                    pass
                    
                    # Fallback to default output loopback if source not found
                    if _current_device is None:
                        _current_device, _kind = self._pick_default_spectrum_source(_sc)
                        self._spec_selected_source = None
                        if _current_device:
                            _tag = "output" if _kind == "output-loopback" else "input"
                            self.log(f"[Spectrum] Using default {_tag} source: {_current_device.name}", color="grey500")

                    # Re-evaluate normalization per source switch/start; do not carry old gain state.
                    if _current_device is not None and (_source_switch or self._spec_gain != 1.0):
                        self._spec_gain = 0.05  # low start so attack fires immediately for quiet sources
                        self._reset_spec_analysis_state()
                        self._spec_vu_gain = 0.18
                        self._spec_vu_left = 0.0
                        self._spec_vu_right = 0.0
                        self._spec_vu_peak_left = 0.0
                        self._spec_vu_peak_right = 0.0
                        self._spec_idle_active = False
                        self._spec_last_audio_ts = time.monotonic()

                if _current_device is None:
                    if not self._spec_no_audio_warned:
                        self._spec_no_audio_warned = True
                        self.log("[Spectrum] No microphone/loopback device found. Enable 'Stereo Mix' in Windows Sound Settings.", color="orange400")
                    time.sleep(2.0)
                    continue

                _sr = int(getattr(self, "_spec_sample_rate", 48000) or 48000)
                if _sr not in (16000, 22050, 32000, 44100, 48000):
                    _sr = 48000

                # Lower sample rates are intended for lower CPU machines.
                # Keep FFT cost proportional to sample-rate tier.
                _analysis_bands = max(6, min(int(self._spec_bands), int(getattr(self, "_spec_analysis_bands", self._spec_bands) or self._spec_bands)))
                _n = 1024 if _sr >= 32000 else 512
                _frame_n = max(_n, min(2048, int(_sr / 24)))
                _freqs = _np.fft.rfftfreq(_n, d=1.0 / _sr)
                _edges = _np.geomspace(40.0, 15000.0, _analysis_bands + 1)
                _bins = []
                for i in range(_analysis_bands):
                    lo = int(_np.searchsorted(_freqs, _edges[i], side="left"))
                    hi = int(_np.searchsorted(_freqs, _edges[i + 1], side="right"))
                    if hi <= lo:
                        hi = min(len(_freqs), lo + 1)
                    _bins.append((lo, hi))

                # Prepare log-frequency centers used for per-frame visual EQ interpolation.
                _band_centers = _np.sqrt(_edges[:-1] * _edges[1:])
                _band_centers_log = _np.log10(_band_centers)
                _eq_freqs_log = _np.log10(_np.asarray(self._spec_eq_freqs, dtype=float))

                import warnings as _warnings
                _warnings.filterwarnings("ignore", message="data discontinuity", category=Warning)
                with _current_device.recorder(samplerate=_sr, channels=int(self._spec_capture_channels), blocksize=_frame_n) as _rec:
                    _last_render = 0.0
                    while self.running and not self._spec_source_changed and not self._spec_disabled:
                        _render_interval = self._get_spec_render_interval()
                        _buf = _rec.record(numframes=_frame_n)
                        _arr_raw = _np.asarray(_buf)
                        if _arr_raw.size < _n:
                            time.sleep(0.01)
                            continue

                        # Keep SA processing mono while also extracting true stereo L/R VU levels.
                        if _arr_raw.ndim == 2 and _arr_raw.shape[1] >= 2:
                            _left = _arr_raw[:, 0].reshape(-1)
                            _right = _arr_raw[:, 1].reshape(-1)
                            _arr = ((_left + _right) * 0.5).reshape(-1)
                        else:
                            _arr = _arr_raw.reshape(-1)
                            _left = _arr
                            _right = _arr

                        _vu_n = min(_n, len(_left), len(_right))
                        if _vu_n > 0:
                            _l_lvl = float(_np.sqrt(_np.mean(_left[-_vu_n:] ** 2)))
                            _r_lvl = float(_np.sqrt(_np.mean(_right[-_vu_n:] ** 2)))
                        else:
                            _l_lvl = 0.0
                            _r_lvl = 0.0

                        _arr = _arr[-_n:] * _np.hanning(_n)
                        _spec = _np.abs(_np.fft.rfft(_arr))

                        _vals = []
                        for lo, hi in _bins:
                            _vals.append(float(_spec[lo:hi].max()) if hi > lo else 0.0)

                        _vals = _np.asarray(_vals)
                        _vals = _np.log1p(_vals * 30.0)

                        # Per-band adaptive floor: tracks each band's running average and
                        # subtracts it so only deviations above the floor are displayed.
                        # Fast attack (0.06) so rising noise floors are tracked within ~0.4s;
                        # slow release (0.005) so transients/beats stay visible above the avg.
                        _avg_arr = _np.asarray(self._spec_band_avg, dtype=float)
                        if _avg_arr.size != _vals.size:
                            self._spec_source_changed = True
                            continue
                        _rising = _vals > _avg_arr
                        self._spec_band_avg = list(_np.where(
                            _rising,
                            _avg_arr * 0.94 + _vals * 0.06,
                            _avg_arr * 0.995 + _vals * 0.005,
                        ))
                        _vals = _np.maximum(0.0, _vals - _avg_arr * 0.85)

                        _mx = float(_vals.max()) if _vals.size else 0.0

                        if _mx > 0:
                            # Two-way AGC: fast attack to catch loud peaks, slow release to
                            # normalize quiet sources (loopback audio is often low amplitude).
                            if _mx > self._spec_gain:
                                # Fast attack: handles loud bursts and initial normalization
                                self._spec_gain = self._spec_gain * 0.85 + _mx * 0.15
                            else:
                                # Slow release: gain drifts toward current signal max so quiet
                                # sources (speakers at low OS volume) still fill the bars.
                                # Floor prevents silence from pumping the gain to zero.
                                self._spec_gain = max(0.02, self._spec_gain * 0.993 + _mx * 0.007)
                            _vals = _vals / max(self._spec_gain, 1e-6)

                        # Recompute EQ curve live so slider moves affect the analyzer immediately.
                        _eq_curve = _np.interp(
                            _band_centers_log,
                            _eq_freqs_log,
                            _np.asarray(self._spec_eq_gains, dtype=float),
                        )
                        _vals = _vals * self._spec_sensitivity
                        _vals = _vals * _eq_curve

                        _now = time.monotonic()
                        if _mx > float(self._spec_idle_threshold):
                            self._spec_last_audio_ts = _now
                            self._spec_mode_song_switch_armed = True

                        _idle_on = bool(self._spec_idle_enabled) and ((_now - self._spec_last_audio_ts) >= float(self._spec_idle_timeout))
                        self._spec_idle_active = _idle_on
                        if _idle_on:
                            if _now - _last_render >= _render_interval:
                                self._render_spectrum()
                                _last_render = _now
                            continue

                        _react = max(0.25, min(3.0, float(self._spec_reactivity)))
                        _bar_dec = max(0.1, min(5.0, float(self._spec_bar_decay)))
                        _peak_dec = max(0.1, min(5.0, float(self._spec_peak_decay)))
                        _rise_lerp = min(0.98, 0.72 * _react)
                        _fall_step = 0.04 * _bar_dec
                        _peak_hold_frames = max(2, int(round(8 / _react)))
                        _peak_drop = 0.02 * _peak_dec

                        for i in range(_analysis_bands):
                            tgt = float(max(0.0, min(1.0, _vals[i])))
                            cur = self._spec_bars[i]
                            if tgt >= cur:
                                cur = cur + (tgt - cur) * _rise_lerp
                            else:
                                cur = max(0.0, cur - _fall_step)
                            self._spec_bars[i] = cur

                            if cur >= self._spec_peaks[i]:
                                self._spec_peaks[i] = cur
                                self._spec_peak_hold[i] = _peak_hold_frames
                            else:
                                if self._spec_peak_hold[i] > 0:
                                    self._spec_peak_hold[i] -= 1
                                else:
                                    self._spec_peaks[i] = max(0.0, self._spec_peaks[i] - _peak_drop)

                        # Stereo VU uses its own envelope and AGC so it does not pin at max,
                        # while still respecting the shared sensitivity slider.
                        _l_env = float(_np.log1p(_l_lvl * 18.0))
                        _r_env = float(_np.log1p(_r_lvl * 18.0))
                        _vu_env_max = max(_l_env, _r_env)
                        if _vu_env_max > 0.0:
                            if _vu_env_max > self._spec_vu_gain:
                                self._spec_vu_gain = self._spec_vu_gain * 0.86 + _vu_env_max * 0.14
                            else:
                                self._spec_vu_gain = max(0.06, self._spec_vu_gain * 0.994 + _vu_env_max * 0.006)

                        _vu_scale = 0.65 * (max(0.1, min(1.5, float(self._spec_sensitivity))) / 0.7)
                        _vu_norm = max(self._spec_vu_gain, 1e-6)
                        _l_tgt = float(max(0.0, min(1.0, (_l_env / _vu_norm) * _vu_scale)))
                        _r_tgt = float(max(0.0, min(1.0, (_r_env / _vu_norm) * _vu_scale)))

                        if _l_tgt >= self._spec_vu_left:
                            self._spec_vu_left = self._spec_vu_left + (_l_tgt - self._spec_vu_left) * _rise_lerp
                        else:
                            self._spec_vu_left = max(0.0, self._spec_vu_left - _fall_step)

                        if _r_tgt >= self._spec_vu_right:
                            self._spec_vu_right = self._spec_vu_right + (_r_tgt - self._spec_vu_right) * _rise_lerp
                        else:
                            self._spec_vu_right = max(0.0, self._spec_vu_right - _fall_step)

                        if self._spec_vu_left >= self._spec_vu_peak_left:
                            self._spec_vu_peak_left = self._spec_vu_left
                        else:
                            self._spec_vu_peak_left = max(0.0, self._spec_vu_peak_left - _peak_drop)

                        if self._spec_vu_right >= self._spec_vu_peak_right:
                            self._spec_vu_peak_right = self._spec_vu_right
                        else:
                            self._spec_vu_peak_right = max(0.0, self._spec_vu_peak_right - _peak_drop)

                        _now = time.monotonic()
                        if _now - _last_render >= _render_interval:
                            self._render_spectrum()
                            _last_render = _now
            except Exception as ex:
                err_str = str(ex).lower()
                if ("channel" in err_str or "channels" in err_str) and self._spec_capture_channels > 1:
                    self._spec_capture_channels = 1
                    self.log("[Spectrum] Selected source does not support stereo capture; using mono fallback.", color="grey500")
                    time.sleep(0.4)
                    continue
                # Detect fatal/unrecoverable errors (numpy compatibility, etc.)
                if "binary mode of fromstring is removed" in err_str:
                    self._spec_disabled = True
                    self.log("[Spectrum] Disabled: soundcard is incompatible with NumPy 2.x in this build. Use NumPy 1.26.4 for analyzer support.", color="orange400")
                    return  # Exit audio loop — don't retry
                
                # Temporary errors: retry after delay
                if self.running:
                    self.log(f"[Spectrum] Audio loop error: {ex}", color="orange400")
                _current_device = None
                time.sleep(1.0)

    def unified_poll_loop(self):
        """Unified polling loop for both WLED and LedFx devices.
        - Fires all WLED device pings concurrently — no waiting for slow/offline devices
        - Collects results within a fixed window and logs a single summary line
        - Polls LedFx API every 3s when running to manage live state
        """
        from concurrent.futures import ThreadPoolExecutor, as_completed

        _wled_round_start = time.time()
        _ledfx_last_poll  = 0
        _offline_skip     = {}
        _ledfx_poll_count = 0
        # Window to wait for ping replies before moving on.
        # Must be >= per-device timeout (1.5s) + retry gaps (0.6s) = ~2.1s per attempt.
        # We allow 3 attempts max so worst-case is ~4.5s — clamp window to 5s.
        POLL_WINDOW = 5.0

        while self.running:
            current_time = time.time()

            # Handle window focus state
            if not self.is_focused and not self.unfocused_updates_enabled:
                time.sleep(UNFOCUSED_PAUSE)
                continue

            # Calculate adaptive WLED polling interval based on device count
            device_count = len(self.wled_devices)
            wled_interval = WLED_BASE_INTERVAL + (device_count // 10) * WLED_SCALE_FACTOR
            wled_interval = min(wled_interval, WLED_MAX_INTERVAL)

            # ── WLED concurrent poll round ────────────────────────────────────
            if current_time - _wled_round_start >= wled_interval:
                _wled_round_start = current_time
                _to_poll = []

                for ip in list(self.wled_devices):
                    if not self.running or (not self.is_focused and not self.unfocused_updates_enabled):
                        break
                    is_offline = self.cards.get(ip, {}).get("_glow_state") == "offline"
                    if is_offline:
                        _offline_skip[ip] = _offline_skip.get(ip, 0) + 1
                        if _offline_skip[ip] % 3 != 0:
                            continue  # only poll offline devices every 3rd round
                    else:
                        _offline_skip.pop(ip, None)
                    _to_poll.append(ip)

                if _to_poll:
                    _round_start = time.time()
                    _ok, _fail = [], []

                    with ThreadPoolExecutor(max_workers=len(_to_poll)) as _ex:
                        _futures = {_ex.submit(self._ping_device, ip): ip for ip in _to_poll}
                        try:
                            for _fut in as_completed(_futures, timeout=POLL_WINDOW):
                                ip = _futures[_fut]
                                try:
                                    result = _fut.result()
                                    if result is False:
                                        _fail.append(ip)
                                    else:
                                        _ok.append(ip)
                                except Exception:
                                    _fail.append(ip)
                        except TimeoutError:
                            # Some devices didn't reply within POLL_WINDOW — mark them as failed
                            _done_ips = set(_ok + _fail)
                            for ip in _to_poll:
                                if ip not in _done_ips:
                                    _fail.append(ip)

                    _elapsed = time.time() - _round_start

                    # Single summary log line
                    _ok_names  = [
                        (self.cards.get(ip, {}).get("name_label") or type("", (), {"value": ip})()).value
                        for ip in _ok
                    ]
                    _fail_names = [
                        (self.cards.get(ip, {}).get("name_label") or type("", (), {"value": ip})()).value
                        for ip in _fail
                    ]
                    _summary = f"[Poll] {len(_ok)}/{len(_to_poll)} replied in {_elapsed:.1f}s"
                    if _fail_names:
                        _summary += f" — timeout: {', '.join(_fail_names)}"
                    self.dbg_unique("wled_poll_summary", _summary)
                else:
                    time.sleep(1)

            # ── LedFx API poll ────────────────────────────────────────────────
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
                                    self.log(f"[LedFx Poll] Mapped {card_name}, {device_ip} — virtual '{vid}', active={active}", color="grey500")
                            elif _debug:
                                dev_type = devices.get(is_device, {}).get("type", "wled")
                                if dev_type == "wled":
                                    # Try to map is_device ID to device name for context
                                    dev_info = devices.get(is_device, {})
                                    dev_name = dev_info.get("config", {}).get("name", is_device)
                                    self.log(f"[LedFx Poll] {dev_name}, ? — orphaned virtual '{vid}', no IP resolved", color="orange400")

                        if device_ip:
                            if device_ip not in ledfx_active or active or streaming:
                                ledfx_active[device_ip] = active or streaming
                            config = v.get("config", {})
                            bri = config.get("brightness", "N/A")
                            effect_name = config.get("effect", {}).get("name", "N/A") if config.get("effect") else "N/A"
                            self._dbg_ledfx_poll(device_ip, vid, active, streaming, bri, effect_name)

                    try:
                        _names = []
                        for _ip in ledfx_active.keys():
                            _nl = self.cards.get(_ip, {}).get("name_label")
                            _names.append(_nl.value if _nl else _ip)
                        if _names:
                            self.dbg_unique("ledfx_poll_summary", "[LedFx Poll] Polled: " + ", ".join(_names) + " (" + str(len(_names)) + ")")
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
                    self.dbg_unique("ledfx_poll_error", f"[LedFx Poll] Error: {e}", color="orange400")

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

    def async_update_status(self, ip, is_online, new_name=None, is_on=None, fx_name=None, current_bri=None, ver=None, arch=None, rssi=None, is_live=False):
        if ip in self.cards and self._is_locked(ip):
          now = time.time()
          last = self._last_defer_log.get(ip, 0)
          if now - last > 1.0:
            self._last_defer_log[ip] = now
            c = self.cards.get(ip, {})
            _nm = c.get("name_label")
            _disp = _nm.value if _nm else ip
            self.dbg(f"[Update] {_disp}, {ip} — ignoring remote updates (user input in progress)", color="orange400")
          return
        if ip in self.cards and not self._is_locked(ip):
            c = self.cards[ip]
            if is_online:
                # --- THE FIX: Reset state immediately to prevent log spam ---
                if c.get("_glow_state") == "offline":
                    display = c["name_label"].value or ip
                    self.log(f"[Device] {display} ({ip}) back ONLINE", color="green400")
                    # Force state out of offline so the NEXT ping doesn't trigger this log
                    c["_glow_state"] = "on" if is_on else "off" 
                # -------------------------------------------------------------

                if new_name:
                    c["name_label"].value = new_name.upper()
                    self.display_names[ip] = new_name.upper()
                if is_on is not None:
                    _prev_sw = c["switch"].value
                    if is_on != _prev_sw:
                        _cn = c.get("name_label")
                        _cname = _cn.value if _cn else ip
                        self.dbg(f"[Update] {_cname}, {ip} — switch changed: on={is_on} (was {_prev_sw})")
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
                            c["update_ver_text"].value = f"v{self.latest_release_ver}"
                            c["update_btn"].visible = True
                        else:
                            # Version matches — hide button even if it was shown before
                            c["update_btn"].visible = False
                
                # --- NEW RECOVERY LOGIC ---
                # If we are live, we still need to clear the "OFFLINE" state
                if ip in self.live_ips:
                    c["status"].value = f"ONLINE ({rssi}%)" if rssi else "ONLINE"
                    c["status"].color = "cyan" # Or "purple700" if you prefer
                    c["status"].visible = True
                    
                    # Ensure we aren't showing the red offline border anymore
                    if c.get("_glow_state") == "offline":
                        c["_glow_state"] = "on"
                        c["glow"].bgcolor = "#0a1a1a" # Back to dark teal/black
                else:
                    # Standard WLED (Not Live) Logic
                    if not self.ledfx_running:
                        c["live_badge"].visible = False
                    
                    c["status"].value = f"ONLINE ({rssi}%)" if rssi else "ONLINE"
                    c["status"].color = "cyan"
                    c["status"].visible = True

                    if is_on is True:
                        c["glow"].bgcolor = "#0a1a1a"
                        c["_glow_state"] = "on"
                    elif is_on is False:
                        c["glow"].bgcolor = "#121420"
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

    def _schedule_status_update(self, ip, is_online, new_name=None, is_on=None, fx_name=None, current_bri=None, ver=None, arch=None, rssi=None, is_live=False):
        """Thread-safe status updater for ping workers and UI thread callers."""
        try:
            if threading.current_thread() is threading.main_thread():
                self.async_update_status(ip, is_online, new_name, is_on, fx_name, current_bri, ver, arch, rssi, is_live)
            else:
                self.page.call_from_thread(
                    lambda: self.async_update_status(ip, is_online, new_name, is_on, fx_name, current_bri, ver, arch, rssi, is_live)
                )
        except Exception:
            try:
                self.async_update_status(ip, is_online, new_name, is_on, fx_name, current_bri, ver, arch, rssi, is_live)
            except Exception:
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
                    ps_val = s.get("ps", -1)
                    self.active_preset[ip] = ps_val
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
                    self._schedule_status_update(ip, True, i.get("name"), is_on, f_name, s.get("bri"), i.get("ver"), i.get("arch"), i.get("wifi", {}).get("signal"))
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
                        
                        _mh_prev_mode = dict(self.mh_mode.get(ip, {}))
                        _mh_prev_rgb = self.mh_last_rgb.get(ip)
                        _mh_prev_bri = self.individual_brightness.get(ip)

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

                        # Human-readable MH button label:
                        # static mode shows color name; effect mode shows effect name.
                        if not is_on:
                            _mh_mode_label = self._mh_label_for_ip(ip)
                        elif pattern == 0x61:
                            _mh_mode_label = _mh_col_name
                        elif 0x25 <= pattern <= 0x38:
                            _mh_mode_label = MH_MODE_NAME_BY_PATTERN.get(pattern, f"EFFECT 0x{pattern:02X}")
                        else:
                            _mh_mode_label = f"MODE 0x{pattern:02X}"

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

                        if (
                            self.mh_mode.get(ip, {}) != _mh_prev_mode or
                            self.mh_last_rgb.get(ip) != _mh_prev_rgb or
                            self.individual_brightness.get(ip) != _mh_prev_bri
                        ):
                            self.save_cache()
                        
                        self.dbg_unique(f"mhping:{ip}", f"Ping {_mh_cn} ({ip}): on={is_on} bri={_mh_bri_pct} {_mh_fx}")
                        self._schedule_status_update(ip, True, is_on=is_on, fx_name=_mh_mode_label, current_bri=(max(1, bri) if is_on else None))
                
                self.fail_counts[ip] = 0
                return  # success
            except Exception as _e:
                _last_error = _e
                if _attempt < 2:
                    time.sleep(0.3)
                    
        # ppp - speed up offline detection            
        # All 3 attempts failed
        _card = self.cards.get(ip, {})
        already_offline = _card.get("_glow_state") == "offline"
        
        # Increment failure count regardless of LedFx status
        self.fail_counts[ip] = self.fail_counts.get(ip, 0) + 1
        
        if not already_offline:
            # Keep timeout detail in debug logs to avoid cluttering normal console.
            self.dbg_unique(f"ping_fail:{ip}",
                            f"[Ping] {_disp} ({ip}) failed 3 attempts: {_last_error}",
                            color="orange400")
        
        # If we've failed consistently, push the offline status to the UI
        if self.fail_counts[ip] > 2:
            self._schedule_status_update(ip, False)
            
        return False # Explicitly return False so the poll loop knows it failed            
              
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

        self._lock_ui(ip)


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

        c = self.cards.get(ip)

        if not c or c.get("_is_custom"):

            return

        # Commit from freshest known source: last drag sample, then slider UI,
        # then event fallback. This avoids stale end-event values.
        try:
            v = int(self._pending_bri.get(ip, c["bri_slider"].value))
        except Exception:
            try:
                v = int(c["bri_slider"].value)
            except Exception:
                v = int(val)

        # Keep widget value aligned with committed value to prevent visual snapback.
        try:
            c["bri_slider"].value = v
        except Exception:
            pass

        self._pending_bri[ip] = v

        self.individual_brightness[ip] = v

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

    def _lock_ui(self, ip, duration=1.5): self.locks[ip] = time.time() + duration
    def _is_locked(self, ip): return ip in self.locks and time.time() < self.locks[ip]
    
    def _apply_cache(self, c):
        """Apply a loaded cache dict to self. Shared by load_cache and backup recovery."""
        def _clamp(v, lo, hi, default):
            try:
                return max(lo, min(hi, float(v)))
            except Exception:
                return default

        self.cached_data = c.get("devices", {})
        self.device_types = c.get("types", {})
        self.card_order = c.get("card_order", [])
        self.current_master_bri = c.get("master_bri", 128)
        self.prev_master_bri = self.current_master_bri
        self.ledfx_path = c.get("ledfx_path")
        self.ledfx_current_ver = c.get("ledfx_ver", "2.0.0")
        self.individual_brightness = c.get("individual_bri", {})
        self.mh_mode = {}
        for _ip, _state in c.get("mh_mode", {}).items():
            if not isinstance(_state, dict):
                continue
            _pattern = _state.get("pattern")
            try:
                _pattern = int(_pattern) if _pattern is not None else None
            except Exception:
                _pattern = None
            try:
                _speed = int(_state.get("speed", 10))
            except Exception:
                _speed = 10
            self.mh_mode[_ip] = {"pattern": _pattern, "speed": _speed}
        self.mh_last_rgb = {}
        for _ip, _rgb in c.get("mh_last_rgb", {}).items():
            if not isinstance(_rgb, (list, tuple)) or len(_rgb) < 3:
                continue
            try:
                self.mh_last_rgb[_ip] = (
                    max(0, min(255, int(_rgb[0]))),
                    max(0, min(255, int(_rgb[1]))),
                    max(0, min(255, int(_rgb[2]))),
                )
            except Exception:
                continue
        self.custom_names = c.get("custom_names", {})
        self.display_names = c.get("display_names", {})
        self.custom_devices = c.get("custom_devices", {})
        for _k, _v in list(self.custom_devices.items()):
            if not isinstance(_v, dict):
                self.custom_devices[_k] = {}
                _v = self.custom_devices[_k]
            _v.setdefault("is_exe", False)
            _v.setdefault("auto_launch_start", False)
            _v.setdefault("auto_close_exit", False)
            if (not bool(_v.get("is_exe", False))) and (not self._is_spotify_url_target(_v.get("url", ""))):
                _v["auto_close_exit"] = False
        _raw_default_meta = c.get("default_custom_cards_meta", {})
        self._default_custom_cards_meta = {
            DEFAULT_WINAMP_CARD_KEY: {"auto_created": False, "user_deleted": False},
            DEFAULT_SPOTIFY_CARD_KEY: {"auto_created": False, "user_deleted": False},
        }
        if isinstance(_raw_default_meta, dict):
            for _k in (DEFAULT_WINAMP_CARD_KEY, DEFAULT_SPOTIFY_CARD_KEY):
                _v = _raw_default_meta.get(_k, {}) if isinstance(_raw_default_meta.get(_k, {}), dict) else {}
                self._default_custom_cards_meta[_k]["auto_created"] = bool(_v.get("auto_created", False))
                self._default_custom_cards_meta[_k]["user_deleted"] = bool(_v.get("user_deleted", False))
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
        self.title_speed   = c.get("title_speed",   11.0)
        self.title_color   = c.get("title_color",   "#ff0000")
        self.border_effect = c.get("border_effect", "color_loop")
        self.border_speed  = c.get("border_speed",  11.0)
        self.border_color  = c.get("border_color",  "#ff0000")
        self._spec_selected_source = c.get("spec_audio_source", None)
        _src_order = c.get("spec_source_order", [])
        self._spec_source_order = [str(n) for n in _src_order if isinstance(n, str)] if isinstance(_src_order, list) else []

        self._spec_profiles = {}
        _raw_profiles = c.get("spec_profiles", {})
        if isinstance(_raw_profiles, dict):
            for _k, _v in _raw_profiles.items():
                if not isinstance(_k, str) or not isinstance(_v, dict):
                    continue
                _sens = _v.get("sensitivity", 0.85)
                _react = _v.get("reactivity", 3.0)
                _bar = _v.get("bar_decay", 2.0)
                _peak = _v.get("peak_decay", 1.0)
                _eq = _v.get("eq_gains", [1.0] * len(self._spec_eq_freqs))
                if not isinstance(_eq, list) or len(_eq) != len(self._spec_eq_freqs):
                    _eq = [1.0] * len(self._spec_eq_freqs)
                try:
                    self._spec_profiles[_k] = {
                        "sensitivity": _clamp(_sens, 0.1, 1.5, 0.85),
                        "reactivity": _clamp(_react, 0.25, 3.0, 3.0),
                        "bar_decay": _clamp(_bar, 0.1, 5.0, 2.0),
                        "peak_decay": _clamp(_peak, 0.1, 5.0, 1.0),
                        "eq_gains": [max(0.25, min(3.0, float(x))) for x in _eq],
                    }
                except Exception:
                    continue

        # Legacy fallback values (single global profile from older versions).
        self._spec_sensitivity = _clamp(c.get("spec_sensitivity", 0.85), 0.1, 1.5, 0.85)
        self._spec_reactivity = _clamp(c.get("spec_reactivity", 3.0), 0.25, 3.0, 3.0)
        self._spec_bar_decay = _clamp(c.get("spec_bar_decay", 2.0), 0.1, 5.0, 2.0)
        self._spec_peak_decay = _clamp(c.get("spec_peak_decay", 1.0), 0.1, 5.0, 1.0)
        self._spec_target_fps = int(_clamp(c.get("spec_target_fps", 25), 8, 30, 25))
        self._set_spec_analysis_bands(c.get("spec_analysis_bands", self._spec_bands), restart_audio=False, reset_now=True)
        _sr = int(_clamp(c.get("spec_sample_rate", 48000), 8000, 96000, 48000))
        self._spec_sample_rate = _sr if _sr in (16000, 22050, 32000, 44100, 48000) else 48000
        self._spec_sampling_enabled = bool(c.get("spec_sampling_enabled", True))
        _mode = str(c.get("spec_mode", "classic")).lower()
        self._spec_mode = _mode if _mode in ("classic", "vu", "random", "random_song") else "classic"
        if self._spec_mode in ("random", "random_song"):
            self._advance_spectrum_random_mode()
            self._spec_mode_random_next_ts = time.monotonic() + max(1.0, float(self._spec_mode_random_cycle_seconds))
            self._spec_mode_song_switch_armed = True
        self._spec_idle_enabled = bool(c.get("spec_idle_enabled", True))
        self._spec_idle_timeout = _clamp(c.get("spec_idle_timeout", 2.0), 2.0, 30.0, 2.0)
        _idle_fx = str(c.get("spec_idle_effect", "random")).lower()
        self._spec_idle_effect = _idle_fx if _idle_fx in ("random", "aurora", "pulse", "text", "rainbow", "pacman", "tetris", "invaders", "snake", "starwars") else "random"
        self._spec_idle_speed = _clamp(c.get("spec_idle_speed", 3.0), 0.25, 3.0, 3.0)
        _idle_cycle_saved = c.get("spec_idle_cycle_effects", self._spec_idle_cycle_effects)
        if isinstance(_idle_cycle_saved, list):
            _allowed = ["aurora", "pulse", "text", "rainbow", "pacman", "tetris", "invaders", "snake", "starwars"]
            self._spec_idle_cycle_effects = [x for x in _idle_cycle_saved if isinstance(x, str) and x in _allowed]
            if not self._spec_idle_cycle_effects:
                self._spec_idle_cycle_effects = list(_allowed)
        _eq_saved = c.get("spec_eq_gains", self._spec_eq_gains)
        if isinstance(_eq_saved, list) and len(_eq_saved) == len(self._spec_eq_freqs):
            try:
                self._spec_eq_gains = [max(0.25, min(3.0, float(v))) for v in _eq_saved]
            except Exception:
                self._spec_eq_gains = [1.0] * len(self._spec_eq_freqs)
        else:
            self._spec_eq_gains = [1.0] * len(self._spec_eq_freqs)

        self.debug_on_open = c.get("debug_on_open", False)
        self.log_auto_open = c.get("log_auto_open", False)
        self.unfocused_updates_enabled = c.get("unfocused_updates_enabled", True)
        self.save_logs_to_disk = c.get("save_logs_to_disk", False)
        self.exit_remember_actions = c.get("exit_remember_actions", False)
        self.exit_auto_stop_ledfx = c.get("exit_auto_stop_ledfx", False)
        self.exit_auto_all_off = c.get("exit_auto_all_off", False)
        legacy_scene_auto = c.get("ledfx_auto_start", False)
        self.auto_start_ledfx_on_launch = c.get("auto_start_ledfx_on_launch", legacy_scene_auto)
        self.auto_restore_wled_scene = c.get("auto_restore_wled_scene", legacy_scene_auto)
        self.auto_restore_ledfx_scene = c.get("auto_restore_ledfx_scene", legacy_scene_auto)
        self.last_ledfx_scene_id = c.get("last_ledfx_scene_id")
        self.active_ledfx_scene_id = self.last_ledfx_scene_id
        self.last_wled_scene_idx = c.get("last_wled_scene_idx")
        self._pending_ledfx_scene_restore = bool(self.last_ledfx_scene_id and self.auto_restore_ledfx_scene)

        # Ensure default profile exists, then load profile for current source.
        if "__default__" not in self._spec_profiles:
            self._save_spec_profile(None)

        # Load active source profile after globals are initialized.
        self._load_spec_profile(self._spec_selected_source)
        self._sync_spec_quick_buttons()

        # Initialize unified polling device sets — only add actual WLED/MH devices, not custom launcher cards.
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
            except Exception:
                continue  # try next backup

        # Nothing worked — attempt a salvage pass across ALL json files in the data folder
        self._cache_load_warning = (self._cache_load_warning or "[Cache]") + " — all backups failed, attempting data salvage..."
        salvaged = self._salvage_cache()
        if salvaged:
            self._apply_cache(salvaged)
            self._cache_load_warning += f" Recovered: {', '.join(salvaged.get('_salvage_summary', []))}. Cache saved."
            self._do_save_cache()  # persist the salvaged data immediately
        else:
            self._cache_load_warning += " — salvage found nothing, starting fresh"
            self.cached_data = {}

    def _salvage_cache(self):
        """
        Last-resort recovery: scan every JSON file in LOG_DIR and merge whatever
        recognisable keys we find. Returns a merged dict ready for _apply_cache,
        or None if nothing useful was found.
        Keys harvested: devices, types, card_order, scenes, custom_names,
        display_names, custom_devices, card_ids, device_macs, individual_bri,
        master_bri, ledfx_path, ledfx_ver, win_w, win_h, win_max,
        title_effect, title_speed, title_color, border_effect, border_speed,
        border_color, debug_on_open, log_auto_open, save_logs_to_disk,
        exit_remember_actions, exit_auto_stop_ledfx, exit_auto_all_off,
        auto_start_ledfx_on_launch, auto_restore_wled_scene,
        auto_restore_ledfx_scene, last_ledfx_scene_id.
        """
        _SCALAR_KEYS = {
            "master_bri", "ledfx_path", "ledfx_ver",
            "win_w", "win_h", "win_max",
            "title_effect", "title_speed", "title_color",
            "border_effect", "border_speed", "border_color",
            "debug_on_open", "log_auto_open", "save_logs_to_disk",
            "exit_remember_actions", "exit_auto_stop_ledfx", "exit_auto_all_off",
            "ledfx_auto_start", "auto_start_ledfx_on_launch",
            "auto_restore_wled_scene", "auto_restore_ledfx_scene", "last_ledfx_scene_id",
        }
        _DICT_KEYS = {
            "devices", "types", "custom_names", "display_names",
            "custom_devices", "card_ids", "device_macs", "individual_bri",
            "mh_mode", "mh_last_rgb",
        }
        _LIST_KEYS = {"card_order", "scenes"}

        merged = {}
        found_any = False

        # Collect every .json in LOG_DIR, newest first
        all_json = sorted(
            glob.glob(os.path.join(LOG_DIR, "*.json")),
            key=os.path.getmtime, reverse=True
        )
        # Also check the main cache file path even if it's corrupt
        if CACHE_FILE not in all_json and os.path.exists(CACHE_FILE):
            all_json.insert(0, CACHE_FILE)

        for fpath in all_json:
            try:
                with open(fpath, "r") as f:
                    raw = json.load(f)
                if not isinstance(raw, dict):
                    continue
            except Exception:
                # File is not valid JSON at the top level — try to extract
                # partial data by reading it as text and parsing fragments
                try:
                    with open(fpath, "r", errors="replace") as f:
                        text = f.read()
                    # Attempt a loose loads — sometimes only the tail is corrupt
                    raw = {}
                    for attempt in [text, text[:text.rfind('}') + 1] if '}' in text else ""]:
                        try:
                            raw = json.loads(attempt)
                            break
                        except Exception:
                            continue
                    if not isinstance(raw, dict):
                        continue
                except Exception:
                    continue

            # Merge scalar keys — first file wins
            for k in _SCALAR_KEYS:
                if k not in merged and k in raw:
                    merged[k] = raw[k]
                    found_any = True

            # Merge dict keys — union, first file's value wins per sub-key
            for k in _DICT_KEYS:
                if k in raw and isinstance(raw[k], dict):
                    merged.setdefault(k, {})
                    for sub_k, sub_v in raw[k].items():
                        if sub_k not in merged[k]:
                            merged[k][sub_k] = sub_v
                            found_any = True

            # List keys — first non-empty list wins
            for k in _LIST_KEYS:
                if k not in merged and k in raw and isinstance(raw[k], list) and any(x is not None for x in raw[k]):
                    merged[k] = raw[k]
                    found_any = True

        if not found_any:
            return None

        # Build a human-readable summary of what was recovered
        summary = []
        if merged.get("devices"):
            summary.append(f"{len(merged['devices'])} device(s)")
        if merged.get("scenes") and any(s is not None for s in merged["scenes"]):
            n = sum(1 for s in merged["scenes"] if s is not None)
            summary.append(f"{n} scene(s)")
        if merged.get("custom_devices"):
            summary.append(f"{len(merged['custom_devices'])} custom card(s)")
        if merged.get("custom_names"):
            summary.append(f"{len(merged['custom_names'])} custom name(s)")
        if not summary:
            summary.append("partial settings")
        merged["_salvage_summary"] = summary
        return merged

    def save_cache(self):
        """Schedule a deferred cache write. Rapid calls are coalesced — only one
        write happens after a 2-second quiet period, preventing a new JSON backup
        file from being created on every tiny state change."""
        if self._save_timer is not None:
            self._save_timer.cancel()
        self._save_timer = threading.Timer(2.0, self._do_save_cache)
        self._save_timer.daemon = True
        self._save_timer.start()

    def _do_save_cache(self):
        self._save_timer = None
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
            if getattr(c, "data", None) is not None and getattr(c, "data", None) != "__add_device__"
        ]
        data = {
            "devices": sd,
            "types": st,
            "card_order": card_order,
            "master_bri": self.current_master_bri,
            "ledfx_path": self.ledfx_path,
            "ledfx_ver": self.ledfx_current_ver,
            "individual_bri": self.individual_brightness,
            "mh_mode": self.mh_mode,
            "mh_last_rgb": self.mh_last_rgb,
            "custom_names": self.custom_names,
            "display_names": dn,
            "custom_devices": self.custom_devices,
            "default_custom_cards_meta": self._default_custom_cards_meta,
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
            "spec_audio_source": self._spec_selected_source,
            "spec_source_order": self._spec_source_order,
            "spec_target_fps": int(self._spec_target_fps),
            "spec_analysis_bands": int(self._spec_analysis_bands),
            "spec_sample_rate": int(self._spec_sample_rate),
            "spec_sampling_enabled": bool(self._spec_sampling_enabled),
            "spec_sensitivity": self._spec_sensitivity,
            "spec_reactivity": self._spec_reactivity,
            "spec_bar_decay": self._spec_bar_decay,
            "spec_peak_decay": self._spec_peak_decay,
            "spec_mode": self._spec_mode,
            "spec_idle_enabled": self._spec_idle_enabled,
            "spec_idle_timeout": self._spec_idle_timeout,
            "spec_idle_effect": self._spec_idle_effect,
            "spec_idle_speed": self._spec_idle_speed,
            "spec_idle_cycle_effects": self._spec_idle_cycle_effects,
            "spec_eq_gains": self._spec_eq_gains,
            "spec_profiles": self._spec_profiles,
            "debug_on_open": self.debug_on_open,
            "log_auto_open": self.log_auto_open,
            "unfocused_updates_enabled": self.unfocused_updates_enabled,
            "save_logs_to_disk": self.save_logs_to_disk,
            "exit_remember_actions": self.exit_remember_actions,
            "exit_auto_stop_ledfx": self.exit_auto_stop_ledfx,
            "exit_auto_all_off": self.exit_auto_all_off,
            "auto_start_ledfx_on_launch": self.auto_start_ledfx_on_launch,
            "auto_restore_wled_scene": self.auto_restore_wled_scene,
            "auto_restore_ledfx_scene": self.auto_restore_ledfx_scene,
            "last_ledfx_scene_id": self.last_ledfx_scene_id,
            "last_wled_scene_idx": self.last_wled_scene_idx,
        }
        try:
            # Write one backup per session (at first save only), then only update main file
            if not self._session_backup_written:
                ts = datetime.now().strftime("%Y%m%d_%H%M%S")
                bak_path = os.path.join(LOG_DIR, f"wledcc_cache_backup_{ts}.json")
                with open(bak_path, "w") as f:
                    json.dump(data, f)
                self._session_backup_written = True
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
    def broadcast_power(self, s, wait=False):
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
                            _nm = self.cards.get(ip, {}).get("name_label")
                            _dname = _nm.value if _nm else ip
                            self.dbg(f"[Broadcast] {_dname}, {ip} — MH send error: {_e}", color="orange400")
                    threading.Thread(target=_send, daemon=True).start()

                def _resend(ip, round_num):
                    resend_count[ip] = resend_count.get(ip, 0) + 1
                    if not _is_online(ip):
                        return
                    _nm = self.cards.get(ip, {}).get("name_label")
                    _dname = _nm.value if _nm else ip
                    self.dbg_unique(f"bcast_retry:{ip}",
                        f"[Broadcast][RETRY] {_dname} {status_text} (round {round_num})",
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
                    _nm = self.cards.get(ip, {}).get("name_label")
                    _dname = _nm.value if _nm else ip
                    self.log(f"[Broadcast] {_dname} → {status_text}",
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
                            _nm = self.cards.get(ip, {}).get("name_label")
                            _dname = _nm.value if _nm else ip
                            self.dbg_unique(f"bcast_ok:{ip}",
                                f"[Broadcast][OK] {_dname}",
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
                    def _get_failed_dnames(ip):
                        _nm = self.cards.get(ip, {}).get("name_label")
                        return _nm.value if _nm else ip
                    self.dbg_unique("bcast_failed_list",
                        f"[Broadcast][DBG] Failed/unknown: {', '.join(_get_failed_dnames(ip) for ip in failed)}",
                        color="red400")
                else:
                    self.log(f"[Broadcast] POWER {status_text} — all devices confirmed.", color="green400")

            except Exception as e:
                import traceback
                self.log(f"[Broadcast][ERROR] worker crashed: {e}", color="red400")
                self.log(traceback.format_exc(), color="red400")

        if wait:
            _worker()
        else:
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
        _nm = c.get("name_label")
        _cname = _nm.value if _nm else ip
        self.dbg(f"[Live] {_cname}, {ip} — entered live mode", color="orange400")
        self.live_ips.add(ip)
        # Move device from WLED control to LedFx control
        #ppp -works -disabled to try pinging live devices to get remote status changes
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
       
        # live color purple
        c["live_badge"].visible = True
        # Using purple700 (#7b1fa2) for the primary accents
        c["live_icon"].color = "#7b1fa2" 
        c["live_text"].color = "#7b1fa2"
        
        # Dark purple background to make the border pop
        c["live_badge"].bgcolor = "#1a001a" 
        c["live_badge"].border = ft.border.all(1, "#7b1fa2")
        
        c["live_badge"].tooltip = "LedFx has control — click to release back to WLED"
        c["status"].visible = False
        c["glow"].bgcolor = "#0a1a1a"
        c["glow"].border = ft.border.all(2, self._hue_to_hex(self.rainbow_hue))
        c["_glow_state"] = "on" 
        try: 
            c["card"].update()
            c["glow"].update()
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
        _nm = c.get("name_label")
        _cname = _nm.value if _nm else ip
        self.dbg(f"[Live] {_cname}, {ip} — exited live mode", color="cyan")
        self.live_ips.discard(ip)
        self.lor2_ips.discard(ip)
        # Move device from LedFx control back to WLED control
        self.ledfx_devices.discard(ip)
        #ppp works - disabled to try pinging live devices to get remote status changes
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
        c["glow"].bgcolor = "#121420"
        c["glow"].border = ft.border.all(2, "#2b2b3b")
        c["_glow_state"] = "off"
        try: c["card"].update(); c["glow"].update()
        except: pass
        def _delayed_ping(delay=ping_delay):
            time.sleep(delay)
            _c = self.cards.get(ip)
            _nm = _c.get("name_label") if _c else None
            _cname = _nm.value if _nm else ip
            self.dbg(f"[Live] {_cname}, {ip} — delayed post-live ping")
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
                            self.log(f"[Status Code:] {r.status_code} {r.text}", color="orange400")
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
        self.log(f"[Sanitize] {card_name}, {ip} — started", color="yellow700")

        # Lock button for duration of job
        btn = c["sanitize_btn"]
        btn.disabled = True
        btn.content.value = "SANITIZING..."
        btn.content.color = "orange400"
        try: btn.update()
        except: pass

        try:
            # 1. Fetch and clean presets
            self.log(f"[Sanitize] {card_name}, {ip} — fetching presets")
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
            self.log(f"[Sanitize] {card_name}, {ip} — removed {removed} brightness values, uploading")

            # 2. Upload cleaned presets — ensure all keys are strings for valid JSON
            clean_json = json.dumps(raw, ensure_ascii=False)
            upload_files = {"file": ("presets.json", io.BytesIO(clean_json.encode()))}
            requests.post(f"http://{ip}/upload", files=upload_files)
            self.log(f"[Sanitize] {card_name}, {ip} — upload complete, rebooting")

            # 3. Reboot device so it reloads presets fresh
            btn.content.value = "REBOOTING..."
            try: btn.update()
            except: pass
            try:
                requests.post(f"http://{ip}/json/state", json={"rb": True}, timeout=5)
            except:
                pass  # device cuts connection immediately on reboot — that's normal

            # 4. Wait for device to go offline then come back
            self.log(f"[Sanitize] {card_name}, {ip} — waiting for reboot")
            time.sleep(3)  # give it a moment to actually go down
            for attempt in range(20):
                try:
                    requests.get(f"http://{ip}/json", timeout=3).json()
                    self.log(f"[Sanitize] {card_name}, {ip} — back online, presets are clean", color="green400")
                    self.log(f"[Sanitize] {card_name}, {ip} — note: if WLED web UI is open, close and refresh to load updated presets")
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
            self.log(f"[Sanitize] {card_name}, {ip} — didn't return after reboot, check device manually", color="red400")

        except Exception as e:
            self.log(f"[Sanitize] {card_name}, {ip} — FAILED: {e}", color="red400")

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
                c["glow"].bgcolor = "#121420"
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

                if "ps" in d:
                    state_ps = state.get("ps", -1)
                    requested_ps = int(d["ps"])
                    playlist_first = self.playlist_preset_first.get(ip, {}).get(requested_ps)
                    # Do not use effect-change verification here: playlist presets can
                    # legitimately keep the same current effect, especially on first step.
                    # If WLED reports the preset id back, require an exact match for
                    # normal presets. For playlist presets, also accept the first child
                    # preset id that begins running immediately.
                    allowed_ps = {requested_ps}
                    if playlist_first is not None:
                        allowed_ps.add(int(playlist_first))
                    if state_ps not in (None, -1) and int(state_ps) not in allowed_ps:
                        self.log(
                            f"[CMD] {_disp} attempt {_attempt+1}: preset mismatch — sent ps={requested_ps}, got ps={state_ps}",
                            color="orange400"
                        )
                        mismatch = True

                if not mismatch:
                    if _attempt > 0:
                        self.log(f"[CMD] {_disp} confirmed on attempt {_attempt+1}", color="green400")

                    _is_on = state.get("on")
                    _bri   = state.get("bri")
                    _fx_id = state.get("seg", [{}])[0].get("fx", 0)
                    _fx_name = self.effect_maps.get(ip, {})
                    _fx_str = _fx_name[_fx_id] if isinstance(_fx_name, list) and _fx_id < len(_fx_name) else None

                    self._schedule_status_update(ip, True, None, _is_on, _fx_str, _bri)
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

    def _should_split_header_title(self, w):
        """Return True when header title area should split before the first slider."""
        return w < 1160

    def _apply_header_layout(self, w):
        """Switch title area between one-row and split-row layout."""
        split = self._should_split_header_title(w)
        if split == self._header_title_split:
            return

        if split:
            # Detach controls from the combined row first, then stack rows.
            self._title_combined_row.controls.clear()
            self._title_left_col.controls = [self._title_meta_row, self._title_anim_wrap]
            self._title_left_col.spacing = 2
            self._title_anim_wrap.padding = ft.padding.only(top=12)
            self._title_left_wrap.padding = ft.padding.only(bottom=0)
        else:
            # Move controls back into a single row before restoring the wrapper.
            self._title_left_col.controls = [self._title_combined_row]
            self._title_combined_row.controls = [self._title_meta_row, self._title_anim_wrap]
            self._title_left_col.spacing = 0
            self._title_anim_wrap.padding = ft.padding.only(top=0)
            self._title_left_wrap.padding = ft.padding.only(bottom=0)

        self._header_title_split = split
        try: self.header.update()
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
            self._apply_header_layout(w)
            self._apply_master_layout(w)


    def handle_window_event(self, e):
        if e.data in ["blur", "minimize"]:
            self.is_focused = False
            if self.unfocused_updates_enabled:
                self.log_unique("focus_state", "[Focus] App out of focus — background Log and UI updates still active.  (Configureable in Log Screen).", color="grey500")
            else:
                self.log_unique("focus_state", "[Focus] App out of focus — Log and UI updates paused until focus returns.  (Configureable in Log Screen).", color="grey500")
        elif e.data in ["focus", "restore"]:
            self.is_focused = True
            self.log_unique("focus_state", "[Focus] App focused — Log and UI updates active", color="grey500")
        elif e.data == "close":
            self._show_exit_dialog()

    def cleanup(self, e):
        if self._cleanup_started:
            return
        self._cleanup_started = True
        try:
            self._run_custom_autoclose_on_exit()
        except:
            pass
        self.running = False
        self.brightness_queue.put(None)
        # Flush any pending debounced save before closing
        if self._save_timer is not None:
            self._save_timer.cancel()
            self._save_timer = None
            self._do_save_cache()
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

# wrap flet in instance detector
if __name__ == "__main__":
    # Use the exact title from your app
    if raise_if_running("WLED Command Center+"):
        _sys.exit(0)
    
    def main(page: ft.Page): WLEDApp(page)
    if __name__ == "__main__":
        ft.app(target=main)