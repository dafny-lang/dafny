@echo off
setlocal

set BINARIES=..\..\Binaries
set DAFNY_EXE=%BINARIES%\Dafny.exe

%DAFNY_EXE% /compile:0 /dprint:out.dfy.tmp /verifySeparately %* Two-Way-Sort.dfy Combinators.dfy RingBuffer.dfy RingBufferAuto.dfy Tree.dfy BreadthFirstSearch.dfy

rem for %%f in (
rem     Two-Way-Sort.dfy
rem     Combinators.dfy
rem     RingBuffer.dfy RingBufferAuto.dfy
rem     Tree.dfy
rem     BreadthFirstSearch.dfy
rem   ) do (
rem   echo.
rem   echo -------------------- %%f --------------------
rem   %DAFNY_EXE% /compile:0 /dprint:out.dfy.tmp %* %%f
rem )
