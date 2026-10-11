@echo off
rem ---------------------------------------------------------------------------------------------
rem Re-measures integer division (the one problem that failed) with the improved leaf assist,
rem then runs the impossible-specification control. Results use the prefix  v7_  so they never mix
rem with the earlier  cases_  files.
rem
rem Double-click this file. About 6 minutes for integer division, then about 15 for the control.
rem The hosted model's login is read from  %USERPROFILE%\.formalllm\remote_auth  (one line  user:password,
rem outside the repository). It is never printed and never written anywhere.
rem Stop at any time by closing the window; run the file again and it continues where it stopped.
rem ---------------------------------------------------------------------------------------------
setlocal
cd /d "%~dp0"

if not defined FORMALLLM_REMOTE_AUTH if exist "%USERPROFILE%\.formalllm\remote_auth" set /p FORMALLLM_REMOTE_AUTH=<"%USERPROFILE%\.formalllm\remote_auth"
if not defined FORMALLLM_REMOTE_AUTH goto noauth

where python >nul 2>nul
if errorlevel 1 goto nopython

set "PATH=%USERPROFILE%\.formalllm\rocq\bin;%PATH%"
set PYTHONIOENCODING=utf8

echo.
echo Starting: integer division (20 trials), then the impossible-spec control (5 trials).
echo Progress is saved after every trial.
echo.
python -u benchmarks\reliability_batch.py --prefix v7 --cases D1-intdiv A4-impossible %*
echo.
echo Finished. Results are in benchmarks\results\reliability\  (files starting with  v7_ ).
pause
exit /b 0

:noauth
echo Could not find the model login. Save it as one line  user:password  in
echo   %USERPROFILE%\.formalllm\remote_auth
pause
exit /b 1

:nopython
echo Python was not found on PATH. Open Git Bash instead and follow section 0 of
echo   Reading Material\17_Cookbook_How_To_Run_Everything.md
pause
exit /b 1
