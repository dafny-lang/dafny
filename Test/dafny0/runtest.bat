@echo off
setlocal

set BOOGIEDIR=..\..\Binaries
set DAFNY_EXE=%BOOGIEDIR%\Dafny.exe
set BPLEXE=%BOOGIEDIR%\Boogie.exe

for %%f in (Simple.dfy) do (
  echo.
  echo -------------------- %%f --------------------
  %DAFNY_EXE% %* /dprint:- /env:0 /noVerify %%f
)

for %%f in (TypeTests.dfy NatTypes.dfy SmallTests.dfy Definedness.dfy
            FunctionSpecifications.dfy ResolutionErrors.dfy ParseErrors.dfy
            Array.dfy MultiDimArray.dfy NonGhostQuantifiers.dfy AdvancedLHS.dfy
            Modules0.dfy Modules1.dfy BadFunction.dfy
            Comprehensions.dfy Basics.dfy ControlStructures.dfy
            Termination.dfy DTypes.dfy
            TypeParameters.dfy Datatypes.dfy TypeAntecedents.dfy SplitExpr.dfy
            Refinement.dfy RefinementErrors.dfy) do (
  echo.
  echo -------------------- %%f --------------------
  %DAFNY_EXE% /compile:0 %* %%f
)
