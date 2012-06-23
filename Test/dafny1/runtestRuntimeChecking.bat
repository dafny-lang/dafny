@echo off
setlocal

set BOOGIEDIR=..\..\Binaries
set DAFNY_EXE=%BOOGIEDIR%\Dafny.exe
set BPLEXE=%BOOGIEDIR%\Boogie.exe

REM bugs:
REM SeparationLogicList
REM TreeDatatype
REM MoreInduction

for %%f in (Queue PriorityQueue ExtensibleArray ExtensibleArrayAuto
            BinaryTree UnboundedStack ListCopy ListReverse ListContents
            MatrixFun pow2 SchorrWaite Cubes SumOfCubes FindZero
            TerminationDemos Substitution KatzManna Induction Rippling
            Celebrity BDD UltraFilter) do (
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
