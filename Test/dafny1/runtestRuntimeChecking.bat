@echo off
setlocal

set BOOGIEDIR=..\..\Binaries
set DAFNY_EXE=%BOOGIEDIR%\Dafny.exe
set BPLEXE=%BOOGIEDIR%\Boogie.exe

REM bugs:
REM SeparationLogicList
REM TreeDatatype
REM MoreInduction

REM to implement:
REM Queue              : parallel statements
REM PriorityQueue      : ghost state
REM ExtensibleArray    : ghost state
REM ExtensibleArrayAuto: ghost state
REM BinaryTree         : old expressions
REM UnboundedStack     : ghost state
REM ListCopy           : fresh expressions
REM ListContents       : old expressions
REM SchorrWaite        : ghost state
REM SumOfCubes         : ghost state
REM FindZero           : ghost state
REM TerminationDemos   : ghost state
REM Induction          : quantifiers
REM Celebrity          : quantifiers
REM BDD                : ghost state
REM UltraFilter        : quantifiers

for %%f in (ListReverse MatrixFun pow2 Cubes Substitution KatzManna
            Rippling) do (
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
