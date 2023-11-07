
# Invoking the CLI this way just to stay platform-independent
DAFNY = dotnet run --project ../Dafny --no-build --

DOO_FILE_SOURCE=build/DafnyStandardLibraries-${TARGETLANG}.doo
DOO_FILE_TARGET=binaries/DafnyStandardLibraries-${TARGETLANG}.doo

all: check-binary test check-format check-examples

_build-binary:
	$(DAFNY) build -t:lib src/dfyconfig.toml \
	  `find ./src -name '*-anytarget.dfy'` \
		`find ./src -name '*-${TARGETLANG}*.dfy'` \
		--output:${DOO_FILE_SOURCE}

_check-binary: _build-binary
	unzip -o ${DOO_FILE_SOURCE} -d build/current
	unzip -o ${DOO_FILE_TARGET} -d build/rebuilt
	diff build/current build/rebuilt

_update-binary: _build-binary
	cp ${DOO_FILE_SOURCE} ${DOO_FILE_TARGET}


build-binary-cs: TARGETLANG=cs
build-binary-cs: _build-binary


build-binary-go: TARGETLANG=go
build-binary-go: _build-binary


build-binary-java: TARGETLANG=java
build-binary-java: _build-binary

update-binary-java: TARGETLANG=java
update-binary-java: _update-binary

check-binary-java: TARGETLANG=java
check-binary-java: _check-binary

# For now we only have examples and no dedicated tests.
# We will likely want a test directory as well,
# with deeper coverage of module functionality.

_test-examples:
	$(DAFNY) test -t:${TARGETLANG} examples/dfyconfig.toml `find ./examples -name '*.${TARGETLANG}'` --output:build/stdlibexamples

test-examples-java: TARGETLANG=java
test-examples-java: _test-examples

format:
	$(DAFNY) format .

check-format:
	$(DAFNY) format . --check

check-examples:
	cd build && ../scripts/check-examples `find .. -name '*.md'`

clean:
	rm -rf build
