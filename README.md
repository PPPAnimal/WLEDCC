# WLEDCC - WLED Command Center

WLEDCC is an all-in-one desktop app to discover, control, and automate your WLED, MagicHome, and LedFx devices from a single, modern interface. It features a live spectrum analyzer, scene/preset management, device updates, automation, and custom cards for launching your favorite apps or web pages (like Spotify or Winamp) with Pre/play/pause/next controls.

---

## Features
- **Auto-Discovery:** Instantly finds WLED, MagicHome, and LedFx devices on your network.
- **Unified Control:** Manage all devices from one dashboard—power, color, effects, brightness, scenes, presets, music player controls and more.
- **Spectrum Analyzer:** Live PC audio visualizer featuring 30-band SA, or Left and Rigth VU meter with multiple modes, idle effects, and a 10-band visual EQ.
- **Scene & Preset Management:** Record, play, and organize scenes/presets for both WLED and LedFx.
- **Device Updates:** Handles firmware updates for WLED and installs/updates LedFx, Winamp, and Spotify.
- **Custom Cards:** Add cards to launch any web page (Spotify) or any program (Winamp) with automation options to Start/Stop them on app load/close.
- **Automation:** Exit screen shows options to Auto-start/stop LedFx, auto-load last used scenes, and turn all lights off when you close the app.
- **Logging:** Advanced log panel with debug, auto-open, and save-to-disk options.
- **Platform:** Designed for Windows (Python, Flet UI).

## Device Support
- **WLED:** Full control, create scenes/preset management, firmware updates.
- **MagicHome:** Power, color, mode, and effect control. Creates a MagicHome ↔ LedFx bridge allowing Music reactive support and syncing effects.
- **LedFx:** Scene control, auto-start/stop, and integration with MagicHome Devices.

## Installation
1. **Requirements:**
   - Run installer exe to install this app.
   - in app optional installs
   - Click (Start LEDFX) to get install options.
   - Click (launch) on Winamp card to get install options.
   - Click (launch) on Spotify card to get install options.

2. **Download:**
   - [Latest Release](https://github.com/PPPAnimal/WLEDCC/releases/latest)
   - Or clone this repo and run `WLEDCC.py`.
3. **Run:**
   - `python WLEDCC.py`

## Quick Start
- On first run, WLEDCC will auto-discover devices and add default cards (Winamp, Spotify).
- Use the spectrum analyzer header to visualize PC audio and access spectrum settings.
- Add, edit, or reorder device cards and custom cards from the main dashboard.
- Use the scene bar to switch between WLED and LedFx scenes.
- Configure automation and logging options from the settings and exit popup dialogs.

## Automation & Customization
- **Startup/Exit Automation:** Auto-start LedFx, auto-load last scenes, auto-stop LedFx, and all-off on exit.
- **Per-Card Automation:** Set cards to auto-launch or auto-close with app start/exit.
- **Logging:** Enable debug, auto-open log, and save logs to disk.

## Support & Contributions
If you find WLEDCC useful, consider supporting the developer:

[![Donate via PayPal](https://img.shields.io/badge/Donate-PayPal-blue.svg)](https://paypal.me/BillSullivan02)

- For questions or issues, open an [issue](https://github.com/PPPAnimal/WLEDCC/issues) or email: SullySSignS.ca@gmail.com
- Contributions and feature requests are welcome!

## License
WLEDCC is free software, licensed under the GNU General Public License v3.0 (GPL-3.0).
See [LICENSE](LICENSE) for details.

---

**Created by SullySSignS (PPPAnimal)**