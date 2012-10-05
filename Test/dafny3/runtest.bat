@echo off
setlocal

set BINARIES=..\..\Binaries
set DAFNY_EXE=%BINARIES\Dafny.exe

for %%f in (Iter.dfy) do (
  echo.
  echo -------------------- %%f --------------------
  %DAFNY_EXE% /compile:0 /dprint:out.dfy.tmp %* %%f
)
