
# Invoking the CLI this way just to stay platform-independent
DAFNY = dotnet run --project ../Dafny --no-build --

DOO_FILE_SOURCE=build/DafnyStandardLibraries-${TARGETLANG}.doo
DOO_FILE_TARGET=binaries/DafnyStandardLibraries-${TARGETLANG}.doo

all: check-binary-all test-examples-all check-format check-examples

build-binary:
	$(DAFNY) build -t:lib src/dfyconfig.toml \
	  `find ./src -name '*.dfy' ! -name '*-*.dfy'` \
		`find ./src -name '*-${TARGETLANG}*.dfy'` \
		--output:${DOO_FILE_SOURCE}

check-binary-all:
	make check-binary TARGETLANG=notarget
	make check-binary TARGETLANG=cs
	make check-binary TARGETLANG=java
	make check-binary TARGETLANG=js
	make check-binary TARGETLANG=go
	make check-binary TARGETLANG=py

update-binary-all:
	make update-binary TARGETLANG=notarget
	make update-binary TARGETLANG=cs
	make update-binary TARGETLANG=java
	make update-binary TARGETLANG=js
	make update-binary TARGETLANG=go
	make update-binary TARGETLANG=py
