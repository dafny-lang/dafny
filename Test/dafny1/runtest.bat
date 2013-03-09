@echo off
setlocal

set BINARIES=..\..\Binaries
set DAFNY_EXE=%BINARIES%\Dafny.exe

for %%f in (Queue.dfy PriorityQueue.dfy
            ExtensibleArray.dfy ExtensibleArrayAuto.dfy
            BinaryTree.dfy
            UnboundedStack.dfy
            SeparationLogicList.dfy
            ListCopy.dfy ListReverse.dfy ListContents.dfy
            MatrixFun.dfy pow2.dfy
            ) do (
  echo.
  echo -------------------- %%f --------------------
  %DAFNY_EXE% /compile:0 /vcsMaxKeepGoingSplits:2 /dprint:out.dfy.tmp %* %%f
)

REM ShorrWaite takes a lot longer with /vcsMaxKeepGoingSplits:2, so run it without
for %%f in (SchorrWaite.dfy) do (
  echo.
  echo -------------------- %%f --------------------
  %DAFNY_EXE% /compile:0 /dprint:out.dfy.tmp %* %%f
)

for %%f in (SchorrWaite-stages.dfy
            Cubes.dfy SumOfCubes.dfy FindZero.dfy
            TerminationDemos.dfy Substitution.dfy TreeDatatype.dfy KatzManna.dfy
            Induction.dfy Rippling.dfy MoreInduction.dfy
            Celebrity.dfy BDD.dfy
            UltraFilter.dfy) do (
  echo.
  echo -------------------- %%f --------------------
  %DAFNY_EXE% /compile:0 /vcsMaxKeepGoingSplits:2 /dprint:out.dfy.tmp %* %%f
)
