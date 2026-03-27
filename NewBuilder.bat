@echo off
set /p VERSION=<version.txt
pyinstaller WLEDCC.spec
"D:\Program Files\Inno Setup 7\ISCC.exe" /DMyAppVersion=%VERSION% WLEDCC_setup.iss