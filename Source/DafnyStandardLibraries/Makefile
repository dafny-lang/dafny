
# Invoking the CLI this way just to stay platform-independent
DAFNY = dotnet run --project ../Dafny --no-build --

build:
	$(DAFNY) build -t:lib src/dfyconfig.toml --output:build/stdlib.doo

test:
	$(DAFNY) build -t:lib examples/dfyconfig.toml --output:build/stdlibexamples.doo
	$(DAFNY) test -t:cs build/stdlibexamples.doo
	$(DAFNY) test -t:java build/stdlibexamples.doo
	$(DAFNY) test -t:go build/stdlibexamples.doo
	$(DAFNY) test -t:py build/stdlibexamples.doo
	$(DAFNY) test -t:js build/stdlibexamples.doo

format:
	$(DAFNY) format .

check-format:
	$(DAFNY) format . --check

check-examples:
	scripts/check-examples `find . -name '*.md'`

clean:
	rm -rf build
