@echo off
setlocal

set BINARIES=..\..\Binaries
set DAFNY_EXE=%BINARIES%\Dafny.exe

REM soon again:    SnapshotableTrees.dfy

%DAFNY_EXE% /compile:0 /dprint:out.dfy.tmp /verifySeparately %* Classics.dfy TreeBarrier.dfy COST-verif-comp-2011-1-MaxArray.dfy COST-verif-comp-2011-2-MaxTree-class.dfy COST-verif-comp-2011-2-MaxTree-datatype.dfy COST-verif-comp-2011-3-TwoDuplicates.dfy COST-verif-comp-2011-4-FloydCycleDetect.dfy StoreAndRetrieve.dfy Intervals.dfy TreeFill.dfy TuringFactorial.dfy MajorityVote.dfy SegmentSum.dfy MonotonicHeapstate.dfy Calculations.dfy

rem for %%f in (
rem     Classics.dfy
rem     TreeBarrier.dfy
rem     COST-verif-comp-2011-1-MaxArray.dfy
rem     COST-verif-comp-2011-2-MaxTree-class.dfy
rem     COST-verif-comp-2011-2-MaxTree-datatype.dfy
rem     COST-verif-comp-2011-3-TwoDuplicates.dfy
rem     COST-verif-comp-2011-4-FloydCycleDetect.dfy
rem     StoreAndRetrieve.dfy
rem     Intervals.dfy TreeFill.dfy TuringFactorial.dfy
rem     MajorityVote.dfy SegmentSum.dfy
rem     MonotonicHeapstate.dfy Calculations.dfy
rem   ) do (
rem   echo.
rem   echo -------------------- %%f --------------------
rem   %DAFNY_EXE% /compile:0 /dprint:out.dfy.tmp %* %%f
rem )
