@echo off
setlocal

set BOOGIEDIR=..\..\Binaries
set DAFNY_EXE=%BOOGIEDIR%\Dafny.exe
set CSC=c:/Windows/Microsoft.NET/Framework/v4.0.30319/csc.exe

for %%f in (
    Two-Way-Sort.dfy
    Combinators.dfy
    RingBuffer.dfy
    Tree.dfy
    BreadthFirstSearch.dfy
  ) do (
  echo.
  echo -------------------- %%f --------------------
  %DAFNY_EXE% /compile:0 /dprint:out.dfy.tmp %* %%f
)
