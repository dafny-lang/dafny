@echo off
setlocal

set BINARIES=..\..\Binaries
set DAFNY_EXE=%BINARIES%\Dafny.exe

for %%f in (b1.dfy b2.dfy b3.dfy b4.dfy b5.dfy b6.dfy b7.dfy b8.dfy) do (
  echo.
  echo -------------------- %%f --------------------
  %DAFNY_EXE% /compile:0 %* %%f
)
