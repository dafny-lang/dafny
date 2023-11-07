
# Invoking the CLI this way just to stay platform-independent
DAFNY = dotnet run --project ../Dafny --no-build --

DOO_FILE_SOURCE=build/DafnyStandardLibraries-${TARGETLANG}.doo
DOO_FILE_TARGET=binaries/DafnyStandardLibraries-${TARGETLANG}.doo

all: check-binary-all test-examples-all check-format check-examples

build-binary:
	$(DAFNY) build -t:lib src/dfyconfig.toml \
	  `find ./src -name '*-anytarget.dfy'` \
		`find ./src -name '*-${TARGETLANG}*.dfy'` \
		--output:${DOO_FILE_SOURCE}

check-binary: build-binary
	unzip -o ${DOO_FILE_SOURCE} -d build/current
	unzip -o ${DOO_FILE_TARGET} -d build/rebuilt
	diff build/current build/rebuilt

check-binary-all:
	make check-binary TARGETLANG=notarget
	make check-binary TARGETLANG=cs
	make check-binary TARGETLANG=java
	make check-binary TARGETLANG=js
	make check-binary TARGETLANG=go
	make check-binary TARGETLANG=py

update-binary: build-binary
	cp ${DOO_FILE_SOURCE} ${DOO_FILE_TARGET}

update-binary-all:
	make update-binary TARGETLANG=notarget
	make update-binary TARGETLANG=cs
	make update-binary TARGETLANG=java
	make update-binary TARGETLANG=js
	make update-binary TARGETLANG=go
	make update-binary TARGETLANG=py

# For now we only have examples and no dedicated tests.
# We will likely want a test directory as well,
# with deeper coverage of module functionality.

test-examples:
	$(DAFNY) test -t:${TARGETLANG} examples/dfyconfig.toml `find ./examples -name '*.${TARGETLANG}'` --output:build/stdlibexamples

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
