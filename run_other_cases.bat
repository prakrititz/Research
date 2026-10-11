@echo off
rem ---------------------------------------------------------------------------------------------
rem Runs the reliability study on the benchmark cases other than the square root, then prints a table.
rem
rem Double-click this file, or from a terminal:   run_other_cases.bat [--trials 20] [--cases B2-max] [--dry-run]
rem Quick check first (about a minute):            run_other_cases.bat --cases A2-assign --trials 2
rem
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
echo Starting. A full run is about 12 cases and can take an hour or more. Progress is saved after every trial.
echo.
python -u benchmarks\reliability_batch.py %*
echo.
echo Finished. Results are in benchmarks\results\reliability\  (files starting with  cases_ ).
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
