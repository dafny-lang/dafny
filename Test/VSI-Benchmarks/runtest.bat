@echo off
setlocal

set BINARIES=..\..\Binaries
set DAFNY_EXE=%BINARIES%\Dafny.exe

%DAFNY_EXE% /compile:0 /verifySeparately %* b1.dfy b2.dfy b3.dfy b4.dfy b5.dfy b6.dfy b7.dfy b8.dfy

rem for %%f in (b1.dfy b2.dfy b3.dfy b4.dfy b5.dfy b6.dfy b7.dfy b8.dfy) do (
rem   echo.
rem   echo -------------------- %%f --------------------
rem   %DAFNY_EXE% /compile:0 %* %%f
rem )
