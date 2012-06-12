@echo off
setlocal

set BOOGIEDIR=..\..\Binaries
set DAFNY_EXE=%BOOGIEDIR%\Dafny.exe
set BPLEXE=%BOOGIEDIR%\Boogie.exe

REM soon again: SnapshotableTrees.dfy

REM to implement:
REM Classics                               : ghost state
REM TreeBarrier                            : ghost state
REM COST-verif-comp-2011-1-MaxArray        : ghost state
REM COST-verif-comp-2011-2-MaxTree-class   : ghost state
REM COST-verif-comp-2011-3-TwoDuplicates   : quantifiers
REM COST-verif-comp-2011-4-FloydCycleDetect: quantifiers
REM Intervals                              : ghost state

for %%f in (COST-verif-comp-2011-2-MaxTree-datatype
            StoreAndRetrieve) do (
  echo.
  echo -------------------- %%f --------------------
  %DAFNY_EXE% /nologo /errorTrace:0 /verification:0 /runtimeChecking:1 /compile:2 %* %%f.dfy
  if exist %%f.cs. (
    del %%f.cs
  )
  if exist %%f.exe. (
    del %%f.exe
  )
  if exist %%f.dll. (
    del %%f.dll
  )
  if exist %%f.pdb. (
    del %%f.pdb
  )
  if exist %%f.pdb.original. (
    del %%f.pdb.original
  )
)
