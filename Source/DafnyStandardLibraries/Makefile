
# Invoking the CLI this way just to stay platform-independent
DAFNY = dotnet run --project ../Dafny --no-build --

DOO_FILE_SOURCE=build/DafnyStandardLibraries.doo
DOO_FILE_TARGET=binaries/DafnyStandardLibraries.doo

all: check-binary test check-format check-examples

build-binary:
	$(DAFNY) build -t:lib src/dfyconfig.toml --output:${DOO_FILE_SOURCE}

check-binary: build-binary
	unzip -o ${DOO_FILE_SOURCE} -d build/current
	unzip -o ${DOO_FILE_TARGET} -d build/rebuilt
	diff build/current build/rebuilt

update-binary: build-binary
	cp ${DOO_FILE_SOURCE} ${DOO_FILE_TARGET}

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
