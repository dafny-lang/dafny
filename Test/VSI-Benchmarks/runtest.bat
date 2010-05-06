@echo off
setlocal

set BOOGIEDIR=..\..\Binaries
set DAFNY_EXE=%BOOGIEDIR%\Dafny.exe
set BPLEXE=%BOOGIEDIR%\Boogie.exe



for %%f in ( b1.dfy b2.dfy b3.dfy b4.dfy b5.dfy b6.dfy b7.dfy
             b8.dfy ) do (
  echo.
  echo -------------------- %%f --------------------
  %DAFNY_EXE% /compile:0 %* %%f
)
