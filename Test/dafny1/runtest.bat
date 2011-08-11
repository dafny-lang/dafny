@echo off
setlocal

set BOOGIEDIR=..\..\Binaries
set DAFNY_EXE=%BOOGIEDIR%\Dafny.exe
set BPLEXE=%BOOGIEDIR%\Boogie.exe
set CSC=c:/Windows/Microsoft.NET/Framework/v4.0.30319/csc.exe

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
            MatrixFun.dfy pow2.dfy
            SchorrWaite.dfy
            Cubes.dfy SumOfCubes.dfy FindZero.dfy
            TerminationDemos.dfy Substitution.dfy TreeDatatype.dfy KatzManna.dfy
            Induction.dfy Rippling.dfy
            Celebrity.dfy
            UltraFilter.dfy) do (
  echo.
  echo -------------------- %%f --------------------

  REM The following line will just run the verifier
  IF "%COMPILEDAFNY%"=="" %DAFNY_EXE% /compile:0 /dprint:out.dfy.tmp %* %%f

  REM Alternatively, the following lines also produce C# code and compile it
  IF NOT "%COMPILEDAFNY%"=="" %DAFNY_EXE% %* %%f
  IF NOT "%COMPILEDAFNY%"=="" %CSC% /nologo /debug /t:library /out:out.dll /r:System.Numerics.dll out.cs
)
