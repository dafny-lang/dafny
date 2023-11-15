
# Invoking the CLI this way just to stay platform-independent
DAFNY = dotnet run --project ../Dafny --no-build --

DOO_FILE_SOURCE=build/DafnyStandardLibraries.doo
DOO_FILE_TARGET=binaries/DafnyStandardLibraries.doo

DOO_FILE_ARITHMETIC_SOURCE=build/DafnyStandardLibraries-arithmetic.doo
DOO_FILE_ARITHMETIC_TARGET=binaries/DafnyStandardLibraries-arithmetic.doo

all: check-binary test check-format check-examples

verify:
	$(DAFNY) verify src/dfyconfig.toml
	$(DAFNY) verify src/dfyconfig-arithmetic.toml

build-binary:
	$(DAFNY) build -t:lib src/dfyconfig.toml --output:${DOO_FILE_SOURCE}
	$(DAFNY) build -t:lib src/dfyconfig-arithmetic.toml --output:${DOO_FILE_ARITHMETIC_SOURCE}

check-binary: build-binary
	unzip -o ${DOO_FILE_SOURCE} -d build/current
	unzip -o ${DOO_FILE_TARGET} -d build/rebuilt
	diff build/current build/rebuilt
	unzip -o ${DOO_FILE_ARITHMETIC_SOURCE} -d build/current-arithmetic
	unzip -o ${DOO_FILE_ARITHMETIC_TARGET} -d build/rebuilt-arithmetic
	diff build/current-arithmetic build/rebuilt-arithmetic

update-binary: build-binary
	cp ${DOO_FILE_SOURCE} ${DOO_FILE_TARGET}
	cp ${DOO_FILE_ARITHMETIC_SOURCE} ${DOO_FILE_ARITHMETIC_TARGET}

# For now we only have examples and no dedicated tests.
# We will likely want a test directory as well,
# with deeper coverage of module functionality.
build-examples:
	$(DAFNY) build -t:lib examples/dfyconfig.toml --output:build/stdlibexamples.doo

test-cs: build-examples
	$(DAFNY) test -t:cs build/stdlibexamples.doo examples/BoundedInts/NonDefault.cs --output:build/stdlibexamples --coverage-report:build/testcoverage

test-java: build-examples
	$(DAFNY) test -t:java build/stdlibexamples.doo examples/BoundedInts/Externs/NonDefault.java --output:build/stdlibexamples

test-go: build-examples
	$(DAFNY) test -t:go build/stdlibexamples.doo examples/BoundedInts/NonDefault.go --output:build/stdlibexamples

test-py: build-examples
	$(DAFNY) test -t:py build/stdlibexamples.doo examples/BoundedInts/NonDefault.py --output:build/stdlibexamples

test-js: build-examples
	$(DAFNY) test -t:js build/stdlibexamples.doo examples/BoundedInts/NonDefault.js --output:build/stdlibexamples

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
