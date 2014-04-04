@echo off
setlocal

set BINARIES=..\..\Binaries
set DAFNY_EXE=%BINARIES%\Dafny.exe

for %%f in (Simple.dfy) do (
  echo.
  echo -------------------- %%f --------------------
  %DAFNY_EXE% %* /dprint:- /env:0 /noVerify %%f
)

for %%f in (TypeTests.dfy NatTypes.dfy RealTypes.dfy Definedness.dfy
            FunctionSpecifications.dfy ResolutionErrors.dfy ParseErrors.dfy
            Array.dfy MultiDimArray.dfy NonGhostQuantifiers.dfy AdvancedLHS.dfy
            ModulesCycle.dfy Modules0.dfy Modules1.dfy Modules2.dfy BadFunction.dfy
            Comprehensions.dfy Basics.dfy ControlStructures.dfy
            Termination.dfy DTypes.dfy ParallelResolveErrors.dfy Parallel.dfy
            TypeParameters.dfy Datatypes.dfy StatementExpressions.dfy
            Coinductive.dfy Corecursion.dfy CoResolution.dfy
            CoPrefix.dfy CoinductiveProofs.dfy
            TypeAntecedents.dfy NoTypeArgs.dfy EqualityTypes.dfy SplitExpr.dfy
            LoopModifies.dfy Refinement.dfy RefinementErrors.dfy
            ReturnErrors.dfy ReturnTests.dfy ChainingDisjointTests.dfy
            CallStmtTests.dfy MultiSets.dfy PredExpr.dfy
            Predicates.dfy Skeletons.dfy OpaqueFunctions.dfy
            Maps.dfy LiberalEquality.dfy
            RefinementModificationChecking.dfy TailCalls.dfy
            IteratorResolution.dfy Iterators.dfy
            RankPos.dfy RankNeg.dfy
            Computations.dfy ComputationsNeg.dfy
            Include.dfy AutoReq.dfy DatatypeUpdate.dfy ModifyStmt.dfy SeqSlice.dfy) do (
  echo.
  echo -------------------- %%f --------------------
  %DAFNY_EXE% /compile:0 /print:out.bpl.tmp /dprint:out.dfy.tmp %* %%f
)

for %%f in (Superposition.dfy) do (
  echo.
  echo -------------------- %%f --------------------
  %DAFNY_EXE% /compile:0 /print:out.bpl.tmp /dprint:out.dfy.tmp /tracePOs %* %%f
)

for %%f in (SmallTests.dfy LetExpr.dfy Calculations.dfy) do (
  echo.
  echo -------------------- %%f --------------------
  %DAFNY_EXE% /compile:0 /print:out.bpl.tmp /dprint:out.tmp.dfy %* %%f
  %DAFNY_EXE% /noVerify /compile:0 %* out.tmp.dfy
)

%DAFNY_EXE% %* Compilation.dfy
%DAFNY_EXE% %* CompilationErrors.dfy
