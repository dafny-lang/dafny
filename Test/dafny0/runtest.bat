@echo off
setlocal

set BOOGIEDIR=..\..\Binaries
set DAFNY_EXE=%BOOGIEDIR%\Dafny.exe

for %%f in (Simple.dfy) do (
  echo.
  echo -------------------- %%f --------------------
  %DAFNY_EXE% %* /dprint:- /env:0 /noVerify %%f
)

for %%f in (TypeTests.dfy NatTypes.dfy SmallTests.dfy Definedness.dfy
            FunctionSpecifications.dfy ResolutionErrors.dfy ParseErrors.dfy
            Array.dfy MultiDimArray.dfy NonGhostQuantifiers.dfy AdvancedLHS.dfy
            ModulesCycle.dfy Modules0.dfy Modules1.dfy BadFunction.dfy
            Comprehensions.dfy Basics.dfy ControlStructures.dfy
            Termination.dfy DTypes.dfy ParallelResolveErrors.dfy Parallel.dfy
            TypeParameters.dfy Datatypes.dfy Coinductive.dfy Corecursion.dfy
            TypeAntecedents.dfy NoTypeArgs.dfy EqualityTypes.dfy SplitExpr.dfy
            LoopModifies.dfy Refinement.dfy RefinementErrors.dfy
            ReturnErrors.dfy ReturnTests.dfy ChainingDisjointTests.dfy
            CallStmtTests.dfy MultiSets.dfy PredExpr.dfy LetExpr.dfy
            Predicates.dfy Skeletons.dfy Maps.dfy LiberalEquality.dfy) do (
  echo.
  echo -------------------- %%f --------------------
  %DAFNY_EXE% /compile:0 /print:out.bpl.tmp /dprint:out.dfy.tmp %* %%f
)

for %%f in (SmallTests.dfy LetExpr.dfy) do (
  echo.
  echo -------------------- %%f --------------------
  %DAFNY_EXE% /compile:0 /dprint:out.tmp.dfy %* %%f
  %DAFNY_EXE% /compile:0 %* out.tmp.dfy
)

%DAFNY_EXE% %* Compilation.dfy
