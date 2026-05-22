# WLED Command Center+ — Changelog

---

## 4.7.2

**Spectrum Analyzer — New Display Modes**
- SA is now a standalone app. Main program calls it and docks it to the top of the screen.
- DETACH button opens a separate faster instance. Docked SA shares resources with WLEDCC.
  On older systems, disable the docked SA and use the detached standalone for best performance.
- SA display supports background images (Band Logos) and is resizable with auto aspect toggle.
- Control buttons appear on hover along the top row. Clicking the display area opens Settings.
- Previous/Next buttons on the display manually cycle through modes and sub-modes.

**New Classic group sub-modes:**
- Waveform — single-channel audio waveform
- L/R Wave — dual left/right channel waveform
- Oscilloscope — triggered scope view
- XY Scope — Lissajous figure (Left vs Right channels)

**New Modern series of SA display modes**
- Beat Saber, Neon Cascade, Rock Stage

**New Hallucination series of SA display modes**
- Mirror, Chromatic, Fish Tank, Morphing
- Each has selectable base layers: Waveform, Circular, Particles, Bars
- Morphing has its own base layers: DNA, Rings, Super, Ribbon

**Beat Scanner**
- Live BPM detection with autocorrelation engine.
- Beat flash — white pulse indicator on every detected beat.
- BPM readout and detection confidence shown in the Beat Scanner panel.
- Per-mode beat sensitivity slider so each mode can be tuned independently.
- Rotation to Beat — Hallucination modes animate rotation in response to detected beats.

**SA Settings — Save / Load / Backup**
- SAVE button turns green when you have unsaved changes.
- LOAD popup offers: Last Saved Settings / Factory Defaults / Load Backup.
- Automatic timestamped backup is created before any destructive load or reset.
- Random playback: 2 modes (per-song and timer-based). Checkboxes in settings choose which modes are included.
- Settings split into tabs: SA Settings, Random/Idle, Visual EQ, Sound Sources.

**WLEDCC Settings — Save / Load / Backup**
- New SAVE CONFIG button — explicitly commits your settings to disk.
- New LOAD / RESTORE button — same popup as SA: Last Saved / Factory Defaults / Load Backup.
- Automatic timestamped backup before any reset or restore operation.

**Python/Flet update**
- Converted app to support Python 3.14 and latest dependencies.

**Bug Fixes**
- Fixed power-on state for auto-restore of scenes on startup.
- Improved WLED / LedFx device control toggle behavior.
- Adjusted default SA settings for better out-of-box performance.
- Manual.txt and CHANGELOG.md now ship inside the installer package.
- General stability and UI refinements throughout.

---

## 4.7.0

- Added Music Reactive support for Magic Home devices (not natively supported in LedFx).
  If Magic Home devices exist and LedFx is running, WLEDCC automatically creates a MHBridge
  device registration in LedFx. MHBridge is set to one pixel and streams its effect data to
  WLEDCC, which converts it to Magic Home codes and sends them to the controllers.
  Set this MHBridge device to any LedFx effect to get music reactive effects on MagicHome devices.
- Full debug logs are always written to file now, even if debug mode is off for the console window.
- Added STAR WARS idle effect.
- Added many new VU meters and ability to make your own custom ones.
- Added timer so both VU meters and idle effects can be controlled separately.

---

## 4.6.9

- HOTFIX: `--clear-effects` flag for sound issue crashing LedFx.

---

## 4.6.8

- Support for Spotify app — installs and controls.
- UI improvements.
- Split SA settings and idle effects settings into two separate menus.
- Options for shutting off Spectrum Analyzer and idle effects to improve performance on older systems.
- Reduced SA frame rate option added.
  *(Setting App Name and Card Border effects to solid color also helps performance.)*

---

## 4.6.7

**Spectrum Analyzer**
- Live 30-band spectrum analyzer in the header reacts to PC audio.
- Click the spectrum display or MIC icon to open Spectrum Settings.
- Idle modes arcade pack: Pac-Man, Tetris, Space Invaders, Snake, and more.
- Sensitivity, Reactivity, Bar Decay, Peak Decay tuning controls.
- Modes: Classic, VU (L/R), Random (1 min), Random (Per Song).
- 10-band visual EQ (affects visualization only — does not change Windows audio output).
- EQ presets: Flat, Bass+, Smile, Vocal.

**LedFx Scenes Mode**
- Scene bar can now switch between WLED scenes and LedFx scenes.
- Use the scene mode toggle button in the scene bar.
- WLEDCC fetches current scenes from LedFx when LedFx mode is selected.

**Exit/Startup Automation**
- Stop LedFx automatically on exit.
- Run All Lights Off automatically on exit.
- Auto-start LedFx on app launch.
- Auto-load last WLED scene on startup.
- Auto-load last LedFx scene on startup.

**Custom Card Automation**
- Per-card automation checkboxes: AUTO START (launch on WLEDCC start) and AUTO CLOSE/STOP ON EXIT.

**Spotify Web Card Controls**
- Previous, Play/Pause, Next controls on Spotify cards.
- Now-playing status line when available.

**Winamp Card Controls**
- Previous, Play, Pause, Stop, Next controls.
- If winamp.exe is missing: Install WINAMP, Browse to existing path, or Open downloads page.

**Other**
- Default quick cards added on first run: WINAMP, SPOTIFY.COM.
- Device IP can be edited directly from the card IP field — WLEDCC rebinds live.
- OPEN LOG expanded: DBG on open, Auto-open, Save to disk, BG updates options.
- Bug fix: Brightness sliders now show numerical value.
- Bug fix: Devices now remember last color/brightness between sessions.
- Reduced logs to one per session, 10 max.
- Last used scene button border now glows.

---

## 4.6.6

- Exit popup: on close, choose Stop LedFx / All Off / Close App / Cancel.
  Checkbox to remember choice for future exits (auto-runs on next close, popup still shown).
- Update buttons now show version to download.
- Reboot and Sanitize redesigned as proper buttons.
- JSON: if config missing, loads backup; if corrupted, now fails with proper error messaging.
- LedFx startup wait increased to 5 seconds before scene fetch.
- WLED update button and live badge moved beside brightness slider.
- Minimum border/app-name brightness raised to 25%.
- Added browse-to-EXE for custom cards.
- Added in-app single-instance enforcement (brings running window to front).
- Log and JSON file count now limited.
- Scan optimized: faster multi-pass instead of one slow 30-second scan.
