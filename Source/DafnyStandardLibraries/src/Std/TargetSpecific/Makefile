
# This Makefile builds the individual DafnyStandardLibraries-<target>.doo
# binary files, containing libraries that are defined differently for
# different target languages.
# Currently this is only FileIO, but the source file naming pattern
# used here should work for others as well.
# DafnyStandardLibraries-notarget is used for non-compiled contexts
# such as `dafny verify`.

# Invoking the CLI this way just to stay platform-independent
DAFNY_DRIVER = dotnet run --project ../../../../DafnyDriver --no-build --

DOO_FILE_SOURCE=../../../build/DafnyStandardLibraries-${TARGETLANG}.doo
DOO_FILE_TARGET=../../../binaries/DafnyStandardLibraries-${TARGETLANG}.doo

verify: build-binary
verify-all: build-binary-all

build-binary:
	mkdir -p ../../../binaries
	$(DAFNY_DRIVER) build -t:lib dfyconfig.toml \
		`find . -name '*-${TARGETLANG}*.dfy'` \
		--output:$(DOO_FILE_SOURCE)
	cp $(DOO_FILE_SOURCE) $(DOO_FILE_TARGET)

build-binary-all:
	make build-binary TARGETLANG=notarget
	make build-binary TARGETLANG=cs
	make build-binary TARGETLANG=java
	make build-binary TARGETLANG=js
	make build-binary TARGETLANG=go
	make build-binary TARGETLANG=py
