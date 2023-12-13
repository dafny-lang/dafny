
# Invoking the CLI this way just to stay platform-independent
DAFNY = dotnet run --project ../Dafny --no-build --

DOO_FILE_SOURCE=build/DafnyStandardLibraries.doo
DOO_FILE_TARGET=binaries/DafnyStandardLibraries.doo
TARGET_EXTERNS=$(wildcard src/${TARGETNAME}/*.${TARGETLANG}) $(wildcard src/${TARGETNAME}/*/*.${TARGETLANG})

all: check-binary test check-format check-examples

verify:
	$(DAFNY) verify src/Std/dfyconfig.toml
	make -C src/Std/TargetSpecific verify-all

build-binary:
	$(DAFNY) build -t:lib src/Shared/Std/dfyconfig.toml --output:${DOO_FILE_SOURCE}

check-binary: build-binary
	unzip -o ${DOO_FILE_SOURCE} -d build/current
	unzip -o ${DOO_FILE_TARGET} -d build/rebuilt
	diff build/current build/rebuilt
	make -C src/Std/TargetSpecific check-binary-all

translate:
	$(DAFNY) translate ${TARGETLANG} "src/${TARGETNAME}/dfyconfig.toml" --output:binaries/${TARGETNAME}/translated
	mkdir -p binaries/${TARGETNAME}
	cp ${TARGET_EXTERNS} binaries/${TARGETNAME}/

update-binary: build-binary
	cp ${DOO_FILE_SOURCE} ${DOO_FILE_TARGET}
# 	make translate TARGETLANG=cs TARGETNAME=CSharp
# 	make translate TARGETLANG=java TARGETNAME=Java
# 	make translate TARGETLANG=js TARGETNAME=JavaScript
# 	make translate TARGETLANG=go TARGETNAME=GoLang
# 	make translate TARGETLANG=py TARGETNAME=Python
	
# Rebuild Dafny to pick up the new embedded assets
	dotnet build ../Dafny.sln

# For now we only have examples and no dedicated tests.
# We will likely want a test directory as well,
# with deeper coverage of module functionality.

test-cs:
	$(DAFNY) test -t:cs --spill-translation examples/dfyconfig.toml examples/BoundedInts/NonDefault.cs --output:build/stdlibexamples --coverage-report:build/testcoverage

test-java:
	$(DAFNY) test -t:java examples/dfyconfig.toml examples/BoundedInts/Externs/NonDefault.java --output:build/stdlibexamples

test-go:
	$(DAFNY) test -t:go examples/dfyconfig.toml examples/BoundedInts/NonDefault.go --output:build/stdlibexamples

test-py:
	$(DAFNY) test  -t:py examples/dfyconfig.toml examples/BoundedInts/NonDefault.py --output:build/stdlibexamples

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
