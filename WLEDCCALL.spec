# WLED Controller + SA - PyInstaller Spec File
# ===============================================
# Builds two EXEs in one run:
#   dist/WLEDCC.exe  — main controller
#   dist/SA.exe      — standalone spectrum analyzer
#
# Run:  pyinstaller WLEDCCALL.spec===============

import sys
from PyInstaller.utils.hooks import collect_all, collect_submodules

flet_datas, flet_binaries, flet_hiddenimports = collect_all('flet')
zeroconf_hiddenimports = collect_submodules('zeroconf')
pil_datas, pil_binaries, pil_hiddenimports = collect_all('PIL')

_common_datas = [
    ('version.txt', '.'),
    ('Manual.txt', '.'),
    ('CHANGELOG.md', '.'),
    ('*.jpg', '.'),
    *flet_datas,
    *pil_datas,
]

_common_binaries = [
    *flet_binaries,
    *pil_binaries,
]

# ── WLEDCC ────────────────────────────────────────────────────────────────────
a_wledcc = Analysis(
    ['wledcc.py'],
    pathex=['.'],
    binaries=_common_binaries,
    datas=_common_datas,
    hiddenimports=[
        *flet_hiddenimports,
        *zeroconf_hiddenimports,
        *pil_hiddenimports,
        'zeroconf._utils.ipaddress',
        'zeroconf._utils.net',
        'psutil',
        'psutil._pswindows',
        'requests',
        'urllib3',
        'certifi',
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
        'importlib',
        'win32gui',
        'win32con',
        'win32api',
        'pywintypes',
        'pythoncom',
        'numpy',
        'soundcard',
        'colorsys',
        'base64',
        'ctypes',
        'math',
        'random',
        'struct',
        'zlib',
        'PIL',
    ],
    excludes=['tkinter', 'matplotlib', 'pandas', 'scipy', 'wx', 'PyQt5', 'PyQt6'],
)

pyz_wledcc = PYZ(a_wledcc.pure)

exe_wledcc = EXE(
    pyz_wledcc,
    a_wledcc.scripts,
    [],                 # Binaries moved to COLLECT
    [],                 # Datas moved to COLLECT
    exclude_binaries=True,
    name='WLEDCC',
    debug=False,
    bootloader_ignore_signals=False,
    strip=False,
    upx=True,
    console=False,
    icon='wledccicon.ico',
)

# ── SA ────────────────────────────────────────────────────────────────────────
a_sa = Analysis(
    ['SA.py'],
    pathex=['.'],
    binaries=_common_binaries,
    datas=_common_datas,
    hiddenimports=[
        *flet_hiddenimports,
        *pil_hiddenimports,
        'threading',
        'json',
        'subprocess',
        'numpy',
        'soundcard',
    ],
    excludes=['tkinter', 'matplotlib', 'pandas', 'scipy', 'wx', 'PyQt5', 'PyQt6'],
)

pyz_sa = PYZ(a_sa.pure)

exe_sa = EXE(
    pyz_sa,
    a_sa.scripts,
    [],                 # Binaries moved to COLLECT
    [],                 # Datas moved to COLLECT
    exclude_binaries=True,
    name='SA',
    debug=False,
    bootloader_ignore_signals=False,
    strip=False,
    upx=True,
    console=False,
    icon='wledccicon.ico',
)

# ── COLLECT (The Shared Folder) ──────────────────────────────────────────────
coll = COLLECT(
    exe_wledcc,
    a_wledcc.binaries,
    a_wledcc.zipfiles,
    a_wledcc.datas,
    exe_sa,
    a_sa.binaries,
    a_sa.zipfiles,
    a_sa.datas,
    strip=False,
    upx=True,
    name='WLEDCC_Shared' # This creates dist/WLEDCC_Shared/
)