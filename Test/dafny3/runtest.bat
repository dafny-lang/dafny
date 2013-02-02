@echo off
setlocal

set BINARIES=..\..\Binaries
set DAFNY_EXE=%BINARIES%\Dafny.exe

for %%f in (
  Iter.dfy Streams.dfy Dijkstra.dfy CachedContainer.dfy
  SimpleInduction.dfy SimpleCoinduction.dfy CalcExample.dfy
  InductionVsCoinduction.dfy Zip.dfy SetIterations.dfy
) do (
  echo.
  echo -------------------- %%f --------------------
  %DAFNY_EXE% /compile:0 /dprint:out.dfy.tmp %* %%f
)
