
# Invoking the CLI this way just to stay platform-independent
DAFNY = dotnet run --project ../Dafny --no-build --

DOO_FILE_SOURCE=build/DafnyStandardLibraries.doo
DOO_FILE_TARGET=binaries/DafnyStandardLibraries.doo

all: check-binary test check-format check-examples

verify:
	$(DAFNY) verify src/Std/dfyconfig.toml
	make -C src/Std/TargetSpecific verify-all

build-binary:
	$(DAFNY) build -t:lib src/Std/dfyconfig.toml --output:${DOO_FILE_SOURCE}

check-binary: build-binary
	unzip -o ${DOO_FILE_SOURCE} -d build/current
	unzip -o ${DOO_FILE_TARGET} -d build/rebuilt
	diff build/current build/rebuilt
	make -C src/Std/TargetSpecific check-binary-all

update-binary: build-binary
	cp ${DOO_FILE_SOURCE} ${DOO_FILE_TARGET}
	make -C src/Std/TargetSpecific update-binary-all
# Rebuild Dafny to pick up the new embedded assets
	dotnet build ../Dafny.sln

# For now we only have examples and no dedicated tests.
# We will likely want a test directory as well,
# with deeper coverage of module functionality.

test-cs:
	$(DAFNY) test -t:cs examples/dfyconfig.toml examples/BoundedInts/NonDefault.cs --output:build/stdlibexamples --coverage-report:build/testcoverage

test-java:
	$(DAFNY) test -t:java examples/dfyconfig.toml examples/BoundedInts/Externs/NonDefault.java --output:build/stdlibexamples

test-go:
	$(DAFNY) test -t:go examples/dfyconfig.toml examples/BoundedInts/NonDefault.go --output:build/stdlibexamples

test-py:
	$(DAFNY) test -t:py examples/dfyconfig.toml examples/BoundedInts/NonDefault.py --output:build/stdlibexamples

test-js:
	$(DAFNY) test -t:js examples/dfyconfig.toml examples/BoundedInts/NonDefault.js --output:build/stdlibexamples

test: test-cs test-java test-go test-py test-js

# We only generate coverage from the C# tests
coverage: test-cs

format:
	$(DAFNY) format .

check-format:
	$(DAFNY) format . --check

check-examples:
	cd build && ../scripts/check-examples `find .. -name '*.md'`

clean:
	rm -rf build
