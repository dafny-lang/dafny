@echo off
setlocal

set BOOGIEDIR=..\..\Binaries
set DAFNY_EXE=%BOOGIEDIR%\Dafny.exe
set BPLEXE=%BOOGIEDIR%\Boogie.exe


for %%f in (Problem1-SumMax.dfy Problem2-Invert.dfy
            Problem3-FindZero.dfy Problem4-Queens.dfy
            Problem5-DoubleEndedQueue.dfy) do (
  echo.
  echo -------------------- %%f --------------------
  %DAFNY_EXE% %* %%f
)
