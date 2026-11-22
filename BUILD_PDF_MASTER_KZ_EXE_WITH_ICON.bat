@echo off
setlocal EnableExtensions
cd /d "%~dp0"
title PDF MASTER KZ - Build EXE with custom icon

echo ============================================
echo  PDF MASTER KZ - EXE BUILDER WITH ICON
echo ============================================
if not exist "PDF_MASTER_KZ.py" (
  echo [ERROR] PDF_MASTER_KZ.py was not found in this folder.
  pause
  exit /b 1
)
if not exist "PDF_MASTER_KZ.ico" (
  echo [ERROR] PDF_MASTER_KZ.ico was not found in this folder.
  pause
  exit /b 1
)

set "PY=python"
where py >nul 2>nul
if not errorlevel 1 (
  py -3.12 --version >nul 2>nul
  if not errorlevel 1 (
    set "PY=py -3.12"
  ) else (
    set "PY=py -3"
  )
)
%PY% --version >nul 2>nul
if errorlevel 1 (
  echo [ERROR] Python 3 is missing.
  pause
  exit /b 1
)
if not exist ".venv\Scripts\python.exe" (
  %PY% -m venv .venv
  if errorlevel 1 goto :fail
)
set "VENV_PY=%CD%\.venv\Scripts\python.exe"
"%VENV_PY%" -m pip install --upgrade pyinstaller pymupdf pillow
if errorlevel 1 goto :fail

echo.
echo [INFO] Building with PDF_MASTER_KZ.ico ...
"%VENV_PY%" -m PyInstaller --noconfirm --clean --onefile --windowed --name PDF_MASTER_KZ --icon "%CD%\PDF_MASTER_KZ.ico" --collect-all pymupdf --hidden-import PIL.ImageTk "PDF_MASTER_KZ.py"
if errorlevel 1 goto :fail

echo.
echo [OK] EXE created: "%CD%\dist\PDF_MASTER_KZ.exe"
echo If Windows Explorer shows the old icon, refresh the icon cache or rename EXE.
pause
exit /b 0
:fail
echo.
echo [ERROR] Build failed. Look above for details.
pause
exit /b 1
