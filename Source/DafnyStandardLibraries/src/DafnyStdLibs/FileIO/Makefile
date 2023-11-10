
# Invoking the CLI this way just to stay platform-independent
DAFNY = dotnet run --project ../../../../Dafny --no-build --

DOO_FILE_SOURCE=../../../build/DafnyStandardLibraries-FileIO-${TARGETLANG}.doo
DOO_FILE_TARGET=../../../binaries/DafnyStandardLibraries-FileIO-${TARGETLANG}.doo

build-binary:
	$(DAFNY) build -t:lib dfyconfig.toml \
	  `find . -name '*.dfy' ! -name '*-*.dfy'` \
		`find . -name '*-${TARGETLANG}*.dfy'` \
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
