
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

test-examples:
	$(DAFNY) test -t:${TARGETLANG} examples/dfyconfig.toml `find ./examples -name '*.${TARGETLANG}'`

test-examples-all:
	make test-examples TARGETLANG=cs
	make test-examples TARGETLANG=java
	make test-examples TARGETLANG=js
	make test-examples TARGETLANG=go
	make test-examples TARGETLANG=py

format:
	$(DAFNY) format .

check-format:
	$(DAFNY) format . --check

check-examples:
	cd build && ../scripts/check-examples `find .. -name '*.md'`

clean:
	rm -rf build
