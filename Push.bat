@echo off
cls
echo ===================================================
echo   WLED Control Center - GitHub Backup (Private)
echo ===================================================
echo.

:: Ask for a quick note on what you changed
set /p commit_msg="What did you update? (e.g. fixed slider bug): "

echo.
echo [1/3] Filtering and Staging files...
:: This uses your .gitignore rules to only grab WLEDCC.py, the installer, etc.
git add .

echo [2/3] Creating a Save Point...
git commit -m "%commit_msg%"

echo [3/3] Uploading to GitHub...
:: This sends your code to the cloud
git push origin main

echo.
echo ===================================================
echo   SUCCESS: Your WLED project is safely backed up!
echo ===================================================
echo.
pause