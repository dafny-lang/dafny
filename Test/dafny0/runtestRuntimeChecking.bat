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
REM SmallTests     : unexpected expressions
REM AdvancedLHS    : fresh expressions
REM BadFunction    : ghost state
REM Basics         : ghost state
REM DTypes         : quantifiers
REM Parallel       : quantifiers
REM TypeParameters : ghost state
REM TypeAntecedents: quantifiers
REM SplitExpr      : ghost state
REM MultiSets      : quantifiers
REM LetExpr        : old expressions
REM Maps           : quantifiers

for %%f in (Simple TypeTests NatTypes Definedness
            FunctionSpecifications ResolutionErrors ParseErrors
            Array MultiDimArray NonGhostQuantifiers ModulesCycle
            Modules0 Comprehensions ControlStructures ParallelResolveErrors
            Coinductive Corecursion LoopModifies Refinement
            RefinementErrors ReturnErrors ChainingDisjointTests
            CallStmtTests PredExpr Skeletons Compilation) do (
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
