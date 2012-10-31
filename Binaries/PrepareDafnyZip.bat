@echo off
setlocal

set DEST_DIR=export

if exist %DEST_DIR% del /q %DEST_DIR%\*
if not exist %DEST_DIR% mkdir %DEST_DIR%

for %%f in (
  AbsInt.dll                          AbsInt.pdb
  Basetypes.dll                       Basetypes.pdb
  BVD.exe                             BVD.pdb
  CodeContractsExtender.dll           CodeContractsExtender.pdb
  Core.dll                            Core.pdb
  Dafny.exe                           Dafny.pdb
  DafnyPrelude.bpl                    DafnyRuntime.cs
  DafnyPipeline.dll                   DafnyPipeline.pdb
  Graph.dll                           Graph.pdb
  Model.dll                           Model.pdb
  ParserHelper.dll                    ParserHelper.pdb
  Provers.SMTLib.dll                  Provers.SMTLib.pdb
  UnivBackPred2.smt2
  VCExpr.dll                          VCExpr.pdb
  VCGeneration.dll                    VCGeneration.pdb
  ..\Source\DafnyExtension\bin\Debug\DafnyLanguageService.vsix
) do (
  copy %%f %DEST_DIR%
)

xcopy /E /I /Y CodeContracts "%DEST_DIR%\CodeContracts"

for %%d in (
  Util Util\emacs Util\vim Util\latex
) do (
  if not exist %DEST_DIR%\%%d mkdir %DEST_DIR%\%%d
)
for %%f in (
  Util\emacs\dafny-mode.el
  Util\vim\dafny.vim
  Util\latex\dafny.sty
) do (
  copy ..\%%f %DEST_DIR%\%%f
)

echo Done.  Now, manually put the contents of the %DEST_DIR% directory into Dafny.zip
