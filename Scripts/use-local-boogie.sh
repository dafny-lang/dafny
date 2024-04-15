BOOGIE_PATH="boogie/"
allDlls=("Boogie.AbstractInterpretation.dll" "Boogie.BaseTypes.dll" "Boogie.CodeContractsExtender.dll" "Boogie.Concurrency.dll" "Boogie.Core.dll" "Boogie.ExecutionEngine.dll" "Boogie.Graph.dll" "Boogie.Houdini.dll" "Boogie.Model.dll" "Boogie.Predication.dll" "Boogie.Provers.SMTLib.dll" "Boogie.VCExpr.dll" "Boogie.VCGeneration.dll" "BoogieDriver.dll" "System.Configuration.ConfigurationManager.dll" "System.Runtime.Caching.dll" "System.Security.Cryptography.ProtectedData.dll" "System.Security.Permissions.dll")
for t in "${allDlls[@]}"
do
	cp "${BOOGIE_PATH}Source/BoogieDriver/bin/Release/net8.0/${t}" Binaries/
done
