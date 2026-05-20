# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Rules

- Always use `async def` for Flet event handlers.
- Use `/plan` mode before changes that touch more than one function, affect more than ~10 lines, or involve architectural decisions. Skip it for targeted 1–3 line fixes where the location and change are fully specified in the request.
- When editing files, provide only the changed lines (diff format) — do not rewrite the whole file.
- **Logging:** When adding new behavior, instrument it with `self.log(message, color, debug=False)`. Use `debug=True` for verbose or high-frequency messages. Include the function name and key values so a failure is self-explaining in the log without needing extra print statements. Use `self.log_unique(key, message)` for messages that would otherwise spam on repeat. After completing an edit or feature, ask the user whether any log entries added for that task should be removed or cleaned up.
- **DRY / reuse first:** Before writing a new code, consider making a helper instead, check if an existing one already does the job. Avoid duplicating large blocks of logic — if multiple features, modes, or controls share similar behavior and one needs a small variation, add a parameter or a one-line override rather than copying the whole helper block. Use judgment: a tiny amount of duplication is fine if sharing it would require over-engineering. The goal is to avoid unnecessary duplication, not abstraction for its own sake.
- **No magic values:** Do not hardcode colors, sizes, timeouts, URLs, port numbers, or other tuneable constants inline. Define them as named constants near the top of the file (or in a dedicated constants block) and reference them by name. One place to change, easy to find.
- **Write for humans:** Keep code readable and linear. Prefer flat, explicit logic over clever one-liners or deeply nested callbacks. A new contributor should be able to read a function top-to-bottom and understand it without tracing five layers of indirection. Avoid spaghetti — if a function is doing too many unrelated things, split it; if two functions are doing the same thing, merge them.
- **Time-based effects, never frame-based:** All animations, lerps, oscillators, and timers must use elapsed wall-clock seconds (`dt = now - last_ts`), not frame counts. Use `alpha = 1.0 - math.exp(-rate * dt)` for exponential smoothing where `rate` is in units of 1/second. This keeps behaviour identical at 30 fps and 60 fps.

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
`WLEDApp` spawns multiple daemon threads that must coordinate carefully — Flet UI updates from background threads **must** use `page.run_task()`, not direct `.update()` calls:

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
`SpectrumController` runs its own audio capture and rendering loop (numpy FFT over `soundcard` input) independently of the Flet event loop. `_PilCanvas` handles PIL-based neon rendering. Idle effect modes (Aurora, Pulse, Text, games) stored in `_spec_idle_*` state.

**Mode hierarchy** — three cascading dropdowns (MODE → TYPE → BASE LAYER):

| MODE (key) | TYPE keys |
|---|---|
| `classic_group` | `classic`, `vu`, `cyber_city`, `hud_reactor` |
| `vu_meters` | `neon_drift`, `retro_tech`, `custom_vu` |
| `modern` | `beat_saber`, `neon_cascade`, `rock_stage` |
| `hallucination` | `mirror`, `chroma`, `perlin`, `morph` |

Hallucination BASE LAYER keys: `waveform`, `circle`, `particles`, `bars`

Per-mode config stored in `_spec_mode_configs`: flat key (e.g. `"classic"`) for non-hallu, three-level path `"hallucination/{submode}/{base}"` for hallu, computed by `_config_path_for()`. Active state tracked in `_spec_mode`, `_spec_hallu_submode`, `_spec_hallu_base_kind`.

**Hallucination state mutation — required pattern:**
Any code that mutates `_spec_hallu_submode` or `_spec_hallu_base_kind` MUST use this exact sequence:
```python
self._spec_mode_transitioning = True
try:
    self._capture_per_mode_settings("hallucination")
    self._spec_hallu_submode    = ...
    self._spec_hallu_base_kind  = ...
    self._spec_hallu_prev_frame = None
    self._spec_hallu_aux        = {}
finally:
    self._spec_mode_transitioning = False
# _apply_per_mode_settings() runs AFTER the flag is cleared
```
The flag blocks the render loop. Skipping it causes the wrong effect to render while the UI shows the correct one. Reset BOTH `_prev_frame` and `_aux`, not just one.

**FPS architecture:**
- `SA_RenderTimer` daemon fires renders at target FPS via `threading.Event.wait()` — decoupled from audio loop; audio loop only updates bar state
- `timeBeginPeriod(1)` called in render thread: raises Windows timer resolution to 1ms (without it, 15.6ms rounding caps all modes at ~32fps)
- All exponential smoothing normalized by `_tscale = actual_block_duration * 24.0` (measured wall-clock, not target FPS) so slider feel is identical at any FPS
- Fast modes (Classic, VU, Hallucination): 50–57fps. PIL modes (NeonCascade, RockStage, BeatSaber, HUDReactor): ~29fps ceiling due to 18–23ms render time
- `_SA_MAX_FPS = 60` in constants block

**SA Config Save/Load Flow:**
`_do_mode_switch()` sequence: `_capture_per_mode_settings(old)` → swap state vars → `_apply_per_mode_settings(new)` → rebuild panel → `_config_dirty = True`. Dirty flag also set on any slider/dropdown/checkbox change; save button turns red. Unsaved changes persist in-session (can test across modes without committing); discarded on close without save. `save_config()` writes all `_spec_mode_configs` with timestamped backup. `load_config(preserve_mode=True)` re-reads disk, discards all in-memory changes.

**Adding a New SA Mode — Checklist:**
When adding any new type key to `_MODE_HIERARCHY`, update ALL FOUR locations in one edit pass or the mode silently falls back to classic spectrum:
1. `_MODE_HIERARCHY` — add `{"key": "...", "label": "..."}` to the group's `submodes`
2. Config-load allowlist (~line 1267) — `_spec_mode = _mode if _mode in (..., "YOUR_KEY", ...) else "classic"`
3. UI mode-selection allowlist (~line 2826) — identical guard in the dropdown `on_change` handler
4. `_neon_vu_theme` setter block (~line 2835) — `elif _mode == "YOUR_KEY": self._neon_vu_theme = "YOUR_KEY"`

Then update `_render_spectrum()`: add key to the membership test, add the `_neon_vu_theme` assignment, add the dispatch `elif`. This bug has been hit 3 times (Waveform, Oscilloscope, XY Scope modes).

**`log_unique` freeze trap (SA.py):** `log_unique` exists on `WLEDApp` only — NOT on `SpectrumController`. Calling `self.log_unique(...)` inside any `_render_spectrum_*` method throws `AttributeError` every frame; `_sync_render` catches it silently so no crash, but the canvas is never updated and the display appears permanently frozen. Use `self._status(msg, debug_only=True)` for SA-side logging.

### Flet Layout Rules
- **Controls cannot live in two layout trees at once.** Only controls explicitly placed in both the wide and narrow master bar rows need `_wide` / `_narrow` paired instances — this is not a blanket rule for all controls. Each pair needs its own `ft.Text` / `ft.Icon` refs so updates reach whichever layout is visible. See `ledfx_btn_wide` / `ledfx_btn_narrow` (~line 3149) as the established pattern.

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
- 'SA-config.json' - Per-mode SA config file

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
