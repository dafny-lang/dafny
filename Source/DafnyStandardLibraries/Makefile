
# Invoking the CLI this way just to stay platform-independent
DAFNY = dotnet run --project ../Dafny --no-build --

build:
	$(DAFNY) build -t:lib src/dfyconfig.toml --output:build/stdlib.doo

test:
	$(DAFNY) test examples/dfyconfig.toml

clean:
	rm -rf build