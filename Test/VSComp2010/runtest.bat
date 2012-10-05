@echo off
setlocal

set BINARIES=..\..\Binaries
set DAFNY_EXE=%BINARIES\Dafny.exe

for %%f in (Problem1-SumMax.dfy Problem2-Invert.dfy
            Problem3-FindZero.dfy Problem4-Queens.dfy
            Problem5-DoubleEndedQueue.dfy) do (
  echo.
  echo -------------------- %%f --------------------
  %DAFNY_EXE% /compile:0 %* %%f
)
