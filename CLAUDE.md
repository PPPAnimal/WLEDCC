# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Rules

- Always use `async def` for Flet event handlers.
- Use `/plan` mode before changes that touch more than one function, affect more than ~10 lines, or involve architectural decisions. Skip it for targeted 1–3 line fixes where the location and change are fully specified in the request.
- When editing files, provide only the changed lines (diff format) — do not rewrite the whole file.
- **Logging:** When adding new behavior, instrument it with the existing `_log()` / debug-log system. Include enough context (function name, key values) that a failure is self-explaining in the log — don't make the user add print statements to find out what went wrong.
- **DRY / reuse first:** Before writing a new helper, look for an existing one that does the same job. UI elements used in more than one place (color swatches, device cards, buttons) must be built by a single factory function or builder method and called everywhere they appear — never duplicated.
- **No magic values:** Do not hardcode colors, sizes, timeouts, URLs, port numbers, or other tuneable constants inline. Define them as named constants near the top of the file (or in a dedicated constants block) and reference them by name. One place to change, easy to find.
- **Write for humans:** Keep code readable and linear. Prefer flat, explicit logic over clever one-liners or deeply nested callbacks. A new contributor should be able to read a function top-to-bottom and understand it without tracing five layers of indirection. Avoid spaghetti — if a function is doing too many unrelated things, split it; if two functions are doing the same thing, merge them.

## Project Overview

**WLEDCC (WLED Command Center+)** is a Windows desktop GUI application for controlling networked LED lighting systems. It manages WLED devices (WiFi LED controllers), integrates with LedFx (music-reactive effects engine), and includes a built-in audio spectrum analyzer.

## Development Commands

**Run the app:**
```powershell
python WLEDCC.py
```

**Install dependencies:**
```powershell
pip install flet numpy soundcard psutil pywin32 requests zeroconf Pillow flux_led
```

**Build distributable (both EXEs + installer):**
```powershell
.\NewBuilderALL.bat
```
This runs PyInstaller with `WLEDCCALL.spec` (produces `dist/WLEDCC.exe` and `dist/SA.exe`), then Inno Setup with `WLEDCC_setupALL.iss`.

**Build EXEs only (no installer):**
```powershell
pyinstaller WLEDCCALL.spec
```

There are no automated tests in this project.

## Architecture

### Entry Points
- **`WLEDCC.py`** — Main application (~10,500 lines). Single `WLEDApp` class wraps all UI, networking, threading, and device logic.
- **`SA.py`** — Standalone spectrum analyzer (~6,000 lines). `SpectrumController` is a self-contained, reusable engine that `WLEDApp` embeds.

### Threading Model
`WLEDApp` spawns multiple daemon threads that must coordinate carefully — Flet UI updates from background threads **must** use `page.run_task()`, not direct `.update()` calls (see memory: `feedback_flet_threadsafe_updates.md`):

| Thread | Purpose |
|---|---|
| `unified_poll_loop` | Central WLED + LedFx device polling (adaptive interval) |
| `brightness_worker` | Debounced slider → device brightness updates |
| `ledfx_monitor_loop` | Monitors LedFx process via psutil |
| `_custom_launcher_monitor_loop` | Monitors custom-card processes |
| `LogFlush` | Drains thread-safe log queue to UI |
| `UIHeartbeat` / `UIWatchdog` | Freeze detection; writes `ui_watchdog.log` |
| `rainbow_loop` | Title/border color animations |

### Device Control Hierarchy
1. **WLED Direct** — HTTP API (`/json/state`, `/json/info`) to device IP
2. **LedFx Live** — Device in live-stream mode; LedFx sends UDP effect data
3. **MagicHome Static** — UDP color/mode packets via `flux_led`
4. **MagicHome Live (MHBridge)** — WLEDCC bridges LedFx effect stream → MagicHome UDP protocol

Discovery uses mDNS (`zeroconf`) for `_http._tcp` services. Device state is cached in `%APPDATA%\Roaming\WLEDCC\wledcc_cache.json` with backup rotation.

### Spectrum Analyzer (`SA.py`)
`SpectrumController` runs its own audio capture and rendering loop independently of the Flet event loop. Key internals:
- numpy FFT over `soundcard` audio input
- Render modes: Classic, VU, CyberCity, BeatSaber, NeonCascade, RockStage, NeonVU, HUDReactor
- Idle effect modes (Aurora, Pulse, Text, games): stored in `_spec_idle_*` state
- Per-mode config persisted separately; `_PilCanvas` handles PIL-based neon rendering

### Flet Layout Rules
- **Controls cannot live in two layout trees at once.** Any control that appears in both `_master_wide` and `_master_narrow` must have separate `_wide` / `_narrow` instances. Follow the established pattern: `ledfx_btn_wide` / `ledfx_btn_narrow`, each with their own paired `ft.Text` / `ft.Icon` refs so updates reach whichever layout is currently visible.

### Flet 0.84 Compatibility Notes
Breaking changes from older Flet versions that are already handled in the code:
- `on_resized` → `on_resize`
- `src_base64` removed → use data URIs (`data:image/png;base64,...`)
- `ft.ImageFit` → `ft.BoxFit`
- Button label updates require `btn.content = ft.Text(...)` not escaped newlines

### Data Storage
All runtime data lives in `%APPDATA%\Roaming\WLEDCC\`:
- `wledcc_cache.json` — device list, config, preset cache
- `wled_session_*.log` — per-session logs
- `ui_watchdog.log` — freeze detection alerts
- Per-mode SA config files

### Key Files
| File | Purpose |
|---|---|
| `WLEDCC.py` | Entire main application |
| `SA.py` | Spectrum analyzer engine |
| `WLEDCCALL.spec` | PyInstaller build spec (both EXEs) |
| `WLEDCC_setupALL.iss` | Inno Setup installer script |
| `NewBuilderALL.bat` | Full build pipeline |
| `@backups/Manual.txt` | User-facing feature manual |
| `A-todo.txt` | Bug tracker / feature backlog |
| `version.txt` | Current version string |
