@echo off
setlocal

set errors=0

if "%1" == "short" goto UseShort

set IncludeLong=True
goto Loop

:UseShort
set IncludeLong=False
shift
goto Loop

:Loop
for /F "eol=; tokens=1,2,3*" %%i in (alltests.txt) do if %%j==Use call runtest.bat %%i %1 %2 %3 %4 %5 %6 %7 %8 %9 || set errors=1

if not %IncludeLong%==True goto End

for /F "eol=; tokens=1,2,3*" %%i in (alltests.txt) do if %%j==Long call runtest.bat %%i %1 %2 %3 %4 %5 %6 %7 %8 %9 || set errors=1

:End
exit /b %errors%