@echo off
setlocal

set BINARIES=..\..\Binaries
set DAFNY_EXE=%BINARIES%\Dafny.exe

%DAFNY_EXE% /compile:0 /verifySeparately /dprint:out.dfy.tmp %* CoqArt-InsertionSort.dfy GHC-MergeSort.dfy Fstar-QuickSort.dfy
