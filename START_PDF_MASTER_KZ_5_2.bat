@echo off
setlocal EnableExtensions
chcp 65001 >nul
cd /d "%~dp0"
title PDF MASTER KZ 5.2 - Windows

set "PYCMD="
where py >nul 2>&1
if not errorlevel 1 (
  py -3.12 -c "import sys" >nul 2>&1
  if not errorlevel 1 set "PYCMD=py -3.12"
  if not defined PYCMD (
    py -3 -c "import sys" >nul 2>&1
    if not errorlevel 1 set "PYCMD=py -3"
  )
)
if not defined PYCMD (
  where python >nul 2>&1
  if not errorlevel 1 set "PYCMD=python"
)
if not defined PYCMD (
  echo [ERROR] Python 3 not found. Install Python 3.12 from python.org.
  pause
  exit /b 1
)

if not exist "PDF_MASTER_KZ.py" (
  echo [ERROR] PDF_MASTER_KZ.py missing from: %CD%
  pause
  exit /b 1
)

%PYCMD% -c "import pymupdf, PIL" >nul 2>&1
if errorlevel 1 (
  echo Installing required packages: pymupdf and pillow...
  %PYCMD% -m pip install --upgrade pymupdf pillow
  if errorlevel 1 (
    echo [ERROR] Package install failed. Check network / Python installation.
    pause
    exit /b 1
  )
)

echo Starting PDF MASTER KZ 5.2...
%PYCMD% "launch_pdf_master.py"
if errorlevel 1 (
  echo.
  echo [ERROR] Check PDF_MASTER_KZ_launch.log or PDF_MASTER_KZ_preview_error.log
  pause
  exit /b 1
)
endlocal
