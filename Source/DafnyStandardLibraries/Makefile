
# Invoking the CLI this way just to stay platform-independent
DAFNY = dotnet run --project ../Dafny --no-build --

build:
	$(DAFNY) build -t:lib src/dfyconfig.toml --output:build/stdlib.doo
	$(DAFNY) translate cs --no-verify src/dfyconfig.toml --output:../DafnyRuntime/DafnyStdLib
# Should be able to do this but a bug means no code is output...
#	$(DAFNY) translate cs build/stdlib.doo --output:../DafnyRuntime/DafnyStdLib

test:
	$(DAFNY) test examples/dfyconfig.toml

clean:
	rm -rf build