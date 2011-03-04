@echo off
setlocal

set BOOGIEDIR=..\..\Binaries
set DAFNY_EXE=%BOOGIEDIR%\Dafny.exe
set BPLEXE=%BOOGIEDIR%\Boogie.exe

for %%f in (BQueue.bpl) do (
  echo.
  echo -------------------- %%f --------------------
  %BPLEXE% %* %%f
)

for %%f in (Queue.dfy PriorityQueue.dfy ExtensibleArray.dfy
            BinaryTree.dfy
            UnboundedStack.dfy
            SeparationLogicList.dfy
            ListCopy.dfy ListReverse.dfy ListContents.dfy
            MatrixFun.dfy
            SchorrWaite.dfy
            Cubes.dfy SumOfCubes.dfy
            TerminationDemos.dfy Substitution.dfy TreeDatatype.dfy KatzManna.dfy
            Induction.dfy
            Celebrity.dfy
            UltraFilter.dfy) do (
  echo.
  echo -------------------- %%f --------------------
  %DAFNY_EXE% /compile:0 %* %%f
)
