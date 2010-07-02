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

for %%f in (TypeTests.dfy SmallTests.dfy Definedness.dfy Array.dfy
            Modules0.dfy Modules1.dfy BadFunction.dfy
            Termination.dfy Use.dfy DTypes.dfy
            TypeParameters.dfy Datatypes.dfy SplitExpr.dfy Refinement.dfy) do (
  echo.
  echo -------------------- %%f --------------------
  %DAFNY_EXE% /compile:0 %* %%f
)
