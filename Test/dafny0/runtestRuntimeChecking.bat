@echo off
setlocal

set BOOGIEDIR=..\..\Binaries
set DAFNY_EXE=%BOOGIEDIR%\Dafny.exe
set BPLEXE=%BOOGIEDIR%\Boogie.exe

REM bugs:
REM Modules1
REM Termination
REM Datatypes
REM NoTypeArgs
REM ReturnTests
REM Predicates

REM to implement:
REM ControlStructures : out parameters is quantifiers

for %%f in (Simple TypeTests NatTypes SmallTests Definedness
            FunctionSpecifications ResolutionErrors ParseErrors
            Array MultiDimArray NonGhostQuantifiers AdvancedLHS
            ModulesCycle Modules0 BadFunction Comprehensions
            Basics DTypes ParallelResolveErrors Parallel
            TypeParameters Coinductive Corecursion
            TypeAntecedents SplitExpr LoopModifies Refinement
            RefinementErrors ReturnErrors ChainingDisjointTests
            CallStmtTests MultiSets PredExpr LetExpr Skeletons
            Maps Compilation) do (
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
