@echo off
cls
echo ===================================================
echo   WLED Control Center - RESTORE FROM CLOUD
echo ===================================================
echo.
echo WARNING: This will overwrite any unsaved local changes!
echo.
set /p confirm="Are you sure you want to restore? (Y/N): "

if /i "%confirm%" neq "Y" goto cancel

echo.
echo [1/2] Fetching latest version from GitHub...
git fetch origin main

echo [2/2] Resetting local files to match Cloud...
git reset --hard origin main

echo.
echo ===================================================
echo   SUCCESS: Your local code is now back to "Last Known Good".
echo ===================================================
pause
exit

:cancel
echo Restore cancelled.
pause