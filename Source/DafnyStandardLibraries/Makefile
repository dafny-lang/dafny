
# Invoking the CLI this way just to stay platform-independent
DAFNY = dotnet run --project ../Dafny --no-build --

build:
	$(DAFNY) build -t:lib src/dfyconfig.toml --output:build/stdlib.doo

test:
	$(DAFNY) test -t:cs examples/dfyconfig.toml
	$(DAFNY) test -t:java examples/dfyconfig.toml
	$(DAFNY) test -t:go examples/dfyconfig.toml
	$(DAFNY) test -t:py examples/dfyconfig.toml
	$(DAFNY) test -t:js examples/dfyconfig.toml
#	$(DAFNY) test -t:rs examples/dfyconfig.toml

clean:
	rm -rf build