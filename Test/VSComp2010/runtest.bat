@echo off
setlocal

set BINARIES=..\..\Binaries
set DAFNY_EXE=%BINARIES%\Dafny.exe

%DAFNY_EXE% /compile:0 /verifySeparately %* Problem1-SumMax.dfy Problem2-Invert.dfy Problem3-FindZero.dfy Problem4-Queens.dfy Problem5-DoubleEndedQueue.dfy

rem for %%f in (Problem1-SumMax.dfy Problem2-Invert.dfy
rem             Problem3-FindZero.dfy Problem4-Queens.dfy
rem             Problem5-DoubleEndedQueue.dfy) do (
rem   echo.
rem   echo -------------------- %%f --------------------
rem   %DAFNY_EXE% /compile:0 %* %%f
rem )
