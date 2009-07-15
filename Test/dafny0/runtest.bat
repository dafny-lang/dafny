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

for %%f in (BQueue.bpl) do (
  echo.
  echo -------------------- %%f --------------------
  %BPLEXE% %* %%f
)

for %%f in (SmallTests.dfy Queue.dfy ListCopy.dfy
            BinaryTree.dfy ListReverse.dfy ListContents.dfy
            SchorrWaite.dfy Termination.dfy Use.dfy DTypes.dfy
            TypeParameters.dfy) do (
  echo.
  echo -------------------- %%f --------------------
  %DAFNY_EXE% %* %%f
)
