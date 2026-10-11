@echo off
rem ---------------------------------------------------------------------------------------------
rem The HumanEval refinement pilot: for 12 hand-checked problems the model derives a verified program
rem (every step proved, then re-checked by Coq), and the program is run on the real HumanEval and
rem EvalPlus tests. Each problem is tried 3 times. The direct-code baseline is printed beside it.
rem
rem Double-click this file, or from a terminal:   run_humaneval_pilot.bat [--repeats 1] [--tasks A B]
rem Quick check first (a few minutes):             run_humaneval_pilot.bat --tasks A --repeats 1
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
echo Starting the HumanEval pilot: 12 problems x 3 tries. Progress is saved after every try.
echo.
python -u -m benchmarks.datasets.he_refine --config gpt-oss-120b-low --repeats 3 --assist --strict 0 --certify coq --out benchmarks\results\datasets\he_refine_pilot.jsonl --baseline benchmarks\results\datasets\direct_baseline_gpt-oss-120b-low_rescored.jsonl %*
echo.
echo Finished. Rows are in benchmarks\results\datasets\he_refine_pilot.jsonl
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
