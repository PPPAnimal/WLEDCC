@echo off
set /p VERSION=<version.txt

echo Installing required Python packages...
pip install Pillow
pip install numpy
pip install soundcard
pip install psutil
pip install pywin32
pip install requests
pip install zeroconf

echo Building executables...
pyinstaller WLEDCCALL.spec
"D:\Program Files\Inno Setup 7\ISCC.exe" /DMyAppVersion=%VERSION% WLEDCC_setupALL.iss

pause
