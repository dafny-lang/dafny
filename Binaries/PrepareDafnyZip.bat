@echo off
setlocal

set DEST_DIR=export

if exist %DEST_DIR% del /q %DEST_DIR%\*
if not exist %DEST_DIR% mkdir %DEST_DIR%

for %%f in (
  BoogieAbsInt.dll                          BoogieAbsInt.pdb
  BoogieBasetypes.dll                       BoogieBasetypes.pdb
  BoogieCodeContractsExtender.dll           BoogieCodeContractsExtender.pdb
  BoogieConcurrency.dll                     BoogieConcurrency.pdb
  BoogieCore.dll                            BoogieCore.pdb
  Dafny.exe                                 Dafny.pdb
  DafnyPipeline.dll                         DafnyPipeline.pdb
  DafnyPrelude.bpl                          DafnyRuntime.cs
  BoogieDoomed.dll                          BoogieDoomed.pdb
  BoogieExecutionEngine.dll                 BoogieExecutionEngine.pdb
  BoogieGraph.dll                           BoogieGraph.pdb
  BoogieHoudini.dll                         BoogieHoudini.pdb
  BoogieModel.dll                           BoogieModel.pdb
  BoogieModelViewer.dll                     BoogieModelViewer.pdb
  BoogieParserHelper.dll                    BoogieParserHelper.pdb
  Provers.SMTLib.dll                        Provers.SMTLib.pdb
  BoogieVCExpr.dll                          BoogieVCExpr.pdb
  BoogieVCGeneration.dll                    BoogieVCGeneration.pdb
  Z3.exe
  Z3-LICENSE.txt
  DafnyLanguageService.vsix
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
  Util\vim\README.md
  Util\latex\dafny.sty
) do (
  copy ..\%%f %DEST_DIR%\%%f
)

echo Done.  Now, manually put the contents of the %DEST_DIR% directory into Dafny.zip
