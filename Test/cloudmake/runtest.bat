@echo off
setlocal

set BINARIES=..\..\Binaries
set DAFNY_EXE=%BINARIES%\Dafny.exe

%DAFNY_EXE% /compile:0 /verifySeparately /dprint:out.dfy.tmp %* CloudMake-ParallelBuilds.dfy CloudMake-CachedBuilds.dfy CloudMake-ConsistentBuilds.dfy
