
# This Makefile builds the individual DafnyStandardLibraries-<target>.doo
# binary files, containing libraries that are defined differently for
# different target languages.
# Currently this is only FileIO, but the source file naming pattern
# used here should work for others as well.
# DafnyStandardLibraries-notarget is used for non-compiled contexts
# such as `dafny verify`.

# Invoking the CLI this way just to stay platform-independent
DAFNY = dotnet run --project ../../../../Dafny --no-build --roll-forward LatestMajor --

NO_VERIFY := false
DOO_FILE_SOURCE=../../../build/DafnyStandardLibraries-${TARGETLANG}.doo
DOO_FILE_TARGET=../../../binaries/DafnyStandardLibraries-${TARGETLANG}.doo

verify: build-binary
verify-all: update-binary-all

build-binary:
	$(DAFNY) build -t:lib --hidden-no-verify=$(NO_VERIFY) dfyconfig.toml \
		`find . -name '*-${TARGETLANG}*.dfy' | sort` \
		--output:${DOO_FILE_SOURCE}

check-binary: build-binary
	unzip -o ${DOO_FILE_SOURCE} -d ../../../build/current-${TARGETLANG}
	unzip -o ${DOO_FILE_TARGET} -d ../../../build/rebuilt-${TARGETLANG}
	diff ../../../build/current-${TARGETLANG} ../../../build/rebuilt-${TARGETLANG}
# Explicitly check for --hidden-no-verify since Dafny itself doesn't
	grep "hidden-no-verify = false" ../../../build/current-${TARGETLANG}/manifest.toml || \
		(echo "ERROR: doo file built with --hidden-no-verify, rebuild without this option" && exit 1)


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

test:
	$(DAFNY) test -t:${TARGETLANG} ../../../examples/TargetSpecific/dfyconfig.toml --output:../../../build/stdlibexamples_targetspecific \
		`find ../../../examples/TargetSpecific -name '*-${TARGETLANG}*.dfy' | sort`

test-all:
	make test TARGETLANG=cs
	make test TARGETLANG=java
	make test TARGETLANG=js
	make test TARGETLANG=go
	make test TARGETLANG=py
