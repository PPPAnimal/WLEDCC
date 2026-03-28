# WLED Controller - PyInstaller Spec File
# ==========================================
# HOW TO USE:
#   1. Place this file in the same folder as your wledcc.py
#   2. Install PyInstaller:       pip install pyinstaller
#   3. Install all dependencies:  pip install flet requests zeroconf psutil
#   4. Run the build:             pyinstaller WLEDCC.spec
#   5. Your EXE will be in:       dist/WLEDCC.exe
#
# To rebuild after changes, just run:  pyinstaller WLEDCC.spec
# ==========================================

import sys
from PyInstaller.utils.hooks import collect_all, collect_submodules

# Collect everything flet needs (it has lots of hidden data files)
flet_datas, flet_binaries, flet_hiddenimports = collect_all('flet')
flet_core_datas, flet_core_binaries, flet_core_hiddenimports = collect_all('flet_core')

# Collect zeroconf submodules (it uses dynamic imports internally)
zeroconf_hiddenimports = collect_submodules('zeroconf')

a = Analysis(
    ['wledcc.py'],           # <-- UPDATE THIS to your current script name
    pathex=['.'],                # Look in current directory
    binaries=[
        *flet_binaries,
        *flet_core_binaries,
    ],
    datas=[
		('version.txt', '.'),
        *flet_datas,
        *flet_core_datas,
    ],
    hiddenimports=[
        # Flet internals
        *flet_hiddenimports,
        *flet_core_hiddenimports,
        # Zeroconf (mDNS device discovery)
        *zeroconf_hiddenimports,
        'zeroconf._utils.ipaddress',
        'zeroconf._utils.net',
        # Networking
        'psutil',
        'psutil._pswindows',
        'requests',
        'urllib3',
        'certifi',
        # Standard lib
        'threading',
        'json',
        'socket',
        'zipfile',
        'queue',
        'io',
        'subprocess',
        'platform',
        'uuid',
        'glob',
        're',
		'win32gui',
		'win32con',
		'win32api',      
        'pywintypes',
        'pythoncom'
    ],
    hookspath=[],
    hooksconfig={},
    runtime_hooks=[],
    excludes=[
        # Trim unused heavy packages to keep EXE smaller
        'tkinter',
        'matplotlib',
        'numpy',
        'pandas',
        'scipy',
        'PIL',
        'wx',
        'PyQt5',
        'PyQt6',
    ],
    noarchive=False,
)

pyz = PYZ(a.pure)

exe = EXE(
    pyz,
    a.scripts,
    a.binaries,
    a.datas,
    [],
    name='WLEDCC',          # Output filename
    debug=False,                     # Set True temporarily if build has errors
    bootloader_ignore_signals=False,
    strip=False,
    upx=True,                        # Compress EXE (requires UPX, safe to leave True)
    upx_exclude=[],
    runtime_tmpdir=None,
    console=False,                   # False = no black console window
    disable_windowed_traceback=False,
    argv_emulation=False,
    target_arch=None,
    codesign_identity=None,
    entitlements_file=None,
    # icon='assets/icon.ico',        # Uncomment and set path if you have an .ico file
)
