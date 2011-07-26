@echo off
setlocal

set BOOGIEDIR=..\..\Binaries
set DAFNY_EXE=%BOOGIEDIR%\Dafny.exe
set BPLEXE=%BOOGIEDIR%\Boogie.exe
set CSC=c:/Windows/Microsoft.NET/Framework/v4.0.30319/csc.exe

for %%f in (b1.dfy b2.dfy b3.dfy b4.dfy b5.dfy b6.dfy b7.dfy b8.dfy) do (
  echo.
  echo -------------------- %%f --------------------

  REM The following line will just run the verifier
  IF "%COMPILEDAFNY%"=="" %DAFNY_EXE% /compile:0 %* %%f

  REM Alternatively, the following lines also produce C# code and compile it
  IF NOT "%COMPILEDAFNY%"=="" %DAFNY_EXE% %* %%f
  IF NOT "%COMPILEDAFNY%"=="" %CSC% /nologo /debug /t:library /out:out.dll /r:System.Numerics.dll out.cs
)
