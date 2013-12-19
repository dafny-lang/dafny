@echo off
setlocal

set BINARIES=..\..\Binaries
set DAFNY_EXE=%BINARIES%\Dafny.exe

%DAFNY_EXE% /compile:0 /verifySeparately %* Iter.dfy Streams.dfy Dijkstra.dfy CachedContainer.dfy SimpleInduction.dfy SimpleCoinduction.dfy CalcExample.dfy InductionVsCoinduction.dfy Zip.dfy SetIterations.dfy Paulson.dfy Filter.dfy WideTrees.dfy InfiniteTrees.dfy OpaqueTrees.dfy GenericSort.dfy

rem for %%f in (
rem   Iter.dfy Streams.dfy Dijkstra.dfy CachedContainer.dfy
rem   SimpleInduction.dfy SimpleCoinduction.dfy CalcExample.dfy
rem   InductionVsCoinduction.dfy Zip.dfy SetIterations.dfy
rem   Paulson.dfy Filter.dfy WideTrees.dfy InfiniteTrees.dfy
rem   OpaqueTrees.dfy GenericSort.dfy
rem ) do (
rem   echo.
rem   echo -------------------- %%f --------------------
rem   %DAFNY_EXE% /compile:0 /dprint:out.dfy.tmp %* %%f
rem )
