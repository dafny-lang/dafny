@echo off
setlocal

set BINARIES=..\..\Binaries
set DAFNY_EXE=%BINARIES%\Dafny.exe

%DAFNY_EXE% /compile:0 /dprint:out.dfy.tmp /verifySeparately %* Queue.dfy PriorityQueue.dfy ExtensibleArray.dfy ExtensibleArrayAuto.dfy BinaryTree.dfy UnboundedStack.dfy SeparationLogicList.dfy ListCopy.dfy ListReverse.dfy ListContents.dfy MatrixFun.dfy pow2.dfy SchorrWaite.dfy SchorrWaite-stages.dfy Cubes.dfy SumOfCubes.dfy FindZero.dfy TerminationDemos.dfy Substitution.dfy TreeDatatype.dfy KatzManna.dfy Induction.dfy Rippling.dfy MoreInduction.dfy Celebrity.dfy BDD.dfy UltraFilter.dfy

rem for %%f in (Queue.dfy PriorityQueue.dfy
rem             ExtensibleArray.dfy ExtensibleArrayAuto.dfy
rem             BinaryTree.dfy
rem             UnboundedStack.dfy
rem             SeparationLogicList.dfy
rem             ListCopy.dfy ListReverse.dfy ListContents.dfy
rem             MatrixFun.dfy pow2.dfy
rem             SchorrWaite.dfy SchorrWaite-stages.dfy
rem             Cubes.dfy SumOfCubes.dfy FindZero.dfy
rem             TerminationDemos.dfy Substitution.dfy TreeDatatype.dfy KatzManna.dfy
rem             Induction.dfy Rippling.dfy MoreInduction.dfy
rem             Celebrity.dfy BDD.dfy
rem             UltraFilter.dfy
rem             ) do (
rem   echo.
rem   echo -------------------- %%f --------------------
rem   %DAFNY_EXE% /compile:0 /dprint:out.dfy.tmp %* %%f
rem )
