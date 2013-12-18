@echo off
setlocal

set BINARIES=..\..\Binaries
set DAFNY_EXE=%BINARIES%\Dafny.exe

%DAFNY_EXE% /compile:0 /verifySeparately %* LazyInitArray.dfy SparseArray.dfy Composite.dfy

rem for %%f in (LazyInitArray.dfy SparseArray.dfy Composite.dfy) do (
rem   echo.
rem   echo -------------------- %%f --------------------
rem   %DAFNY_EXE% /compile:0 %* %%f
rem )
