
# Invoking the CLI this way just to stay platform-independent
DAFNY = dotnet run --project ../Dafny --no-build --

DOO_FILE_SOURCE=build/DafnyStandardLibraries.doo
DOO_FILE_TARGET=binaries/DafnyStandardLibraries.doo

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

# For now we only have examples and no dedicated tests.
# We will likely want a test directory as well,
# with deeper coverage of module functionality.
test:
	$(DAFNY) build -t:lib examples/dfyconfig.toml --output:build/stdlibexamples.doo
	$(DAFNY) test -t:cs build/stdlibexamples.doo examples/BoundedInts/NonDefault.cs --output:build/stdlibexamples
	$(DAFNY) test -t:java build/stdlibexamples.doo examples/BoundedInts/Externs/NonDefault.java --output:build/stdlibexamples
	$(DAFNY) test -t:go build/stdlibexamples.doo examples/BoundedInts/NonDefault.go --output:build/stdlibexamples
	$(DAFNY) test -t:py build/stdlibexamples.doo examples/BoundedInts/NonDefault.py --output:build/stdlibexamples
	$(DAFNY) test -t:js build/stdlibexamples.doo examples/BoundedInts/NonDefault.js --output:build/stdlibexamples
 
format:
	$(DAFNY) format .

check-format:
	$(DAFNY) format . --check

check-examples:
	cd build && ../scripts/check-examples `find .. -name '*.md'`

clean:
	rm -rf build
