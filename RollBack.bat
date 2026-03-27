@echo off
cls
echo ===================================================
echo   WLED Control Center - VERSION ROLLBACK
echo ===================================================
echo.
echo Recent Save Points:
git log -n 5 --oneline
echo.
echo ---------------------------------------------------
echo OPTION A: Type a number (e.g., 1 to go back 1 version)
echo OPTION B: Type a specific 7-character Code (e.g., 4172bd3)
echo ---------------------------------------------------
echo.
set /p target="Where do you want to go back to? "

:: Check if the user entered a small number (1-9) or a long code
echo %target%| findstr /r "^[1-9]$" >nul
if %errorlevel% equ 0 (
    echo [Rolling back %target% step(s)...]
    git reset --hard HEAD~%target%
) else (
    echo [Rolling back to Code: %target%...]
    git reset --hard %target%
)

echo.
echo ===================================================
echo   SUCCESS: You have traveled back in time!
echo ===================================================
pause