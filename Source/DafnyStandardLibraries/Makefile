
# Invoking the CLI this way just to stay platform-independent
DAFNY = dotnet run --project ../Dafny --no-build --

all: build test check-format check-examples

build:
	$(DAFNY) build -t:lib src/dfyconfig.toml --output:build/stdlib.doo

# For now we only have examples and no dedicated tests.
# We will likely want a test directory as well,
# with deeper coverage of module functionality.
test:
	$(DAFNY) build -t:lib examples/dfyconfig.toml --output:build/stdlibexamples.doo
	$(DAFNY) test -t:cs build/stdlibexamples.doo --output:build/stdlibexamples
	$(DAFNY) test -t:java build/stdlibexamples.doo --output:build/stdlibexamples
	$(DAFNY) test -t:go build/stdlibexamples.doo --output:build/stdlibexamples
	$(DAFNY) test -t:py build/stdlibexamples.doo --output:build/stdlibexamples
	$(DAFNY) test -t:js build/stdlibexamples.doo --output:build/stdlibexamples
 
format:
	$(DAFNY) format .

check-format:
	$(DAFNY) format . --check

check-examples:
	cd build && ../scripts/check-examples `find .. -name '*.md'`

clean:
	rm -rf build
