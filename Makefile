# Run these tasks even if eponymous files or folders exist
.PHONY: test-dafny exe

DIR=$(realpath $(dir $(firstword $(MAKEFILE_LIST))))

default: exe

all: exe refman

exe:
	(cd "${DIR}" ; dotnet build Source/Dafny.sln ) ## includes parser

format-dfy:
	(cd "${DIR}"/Source/DafnyCore ; make format)
	(cd "${DIR}"/Source/DafnyStandardLibraries ; make format)

dfy-to-cs: 
	(cd "${DIR}"/Source/DafnyCore ; bash DafnyGeneratedFromDafny.sh)

dfy-to-cs-exe: dfy-to-cs
	(cd "${DIR}" ; dotnet build Source/Dafny.sln )

dfy-to-cs-noverify:
	(cd "${DIR}"/Source/DafnyCore ; bash DafnyGeneratedFromDafny.sh --no-verify)

dfy-to-cs-noverify-exe: dfy-to-cs-noverify exe

boogie: ${DIR}/boogie/Binaries/Boogie.exe

tests:
	(cd "${DIR}"; dotnet test Source/IntegrationTests)

# make test name=<integration test filter>
# make test name=<integration test filter> update=true                to update the test
# make test name=<integration test filter>              build=false   don't build the solution
test:
	@DIR="$(DIR)" name="$(name)" update="$(update)" build="$(build)" bash scripts/test.sh

# Run Dafny on an integration test case directly in the folder itself.
# make test-dafny name=<part of the path> action="run ..." [build=false]
test-dafny:
	@name="$(name)" DIR="$(DIR)" action="$(action)" NO_BUILD=$$( [ "${build}" = "false" ] && echo "true" || echo "false" ) bash scripts/test-dafny.sh

tests-verbose:
	(cd "${DIR}"; dotnet test --logger "console;verbosity=normal" Source/IntegrationTests )

${DIR}/boogie/Binaries/Boogie.exe:
	(cd "${DIR}"/boogie ; dotnet build -c Release Source/Boogie.sln )

refman: exe
	make -C "${DIR}"/docs/DafnyRef

refman-release: exe
	make -C "${DIR}"/docs/DafnyRef release

z3-mac:
	mkdir -p "${DIR}"/Binaries/z3/bin
	wget https://github.com/dafny-lang/solver-builds/releases/download/snapshot-2023-08-02/z3-4.12.1-x64-macos-11-bin.zip
	unzip z3-4.12.1-x64-macos-11-bin.zip
	rm z3-4.12.1-x64-macos-11-bin.zip
	wget https://github.com/dafny-lang/solver-builds/releases/download/snapshot-2023-08-02/z3-4.8.5-x64-macos-11-bin.zip
	unzip z3-4.8.5-x64-macos-11-bin.zip
	rm z3-4.8.5-x64-macos-11-bin.zip
	mv z3-* "${DIR}"/Binaries/z3/bin/
	chmod +x "${DIR}"/Binaries/z3/bin/z3-*

z3-mac-arm:
	mkdir -p "${DIR}"/Binaries/z3/bin
	wget https://github.com/dafny-lang/solver-builds/releases/download/snapshot-2023-08-02/z3-4.12.1-arm64-macos-11-bin.zip
	unzip z3-4.12.1-arm64-macos-11-bin.zip
	rm z3-4.12.1-arm64-macos-11-bin.zip
	wget https://github.com/dafny-lang/solver-builds/releases/download/snapshot-2023-08-02/z3-4.8.5-x64-macos-11-bin.zip
	unzip z3-4.8.5-x64-macos-11-bin.zip
	rm z3-4.8.5-x64-macos-11-bin.zip
	mv z3-* "${DIR}"/Binaries/z3/bin/
	chmod +x "${DIR}"/Binaries/z3/bin/z3-*

z3-ubuntu:
	mkdir -p "${DIR}"/Binaries/z3/bin
	wget https://github.com/dafny-lang/solver-builds/releases/download/snapshot-2023-08-02/z3-4.12.1-x64-ubuntu-20.04-bin.zip
	unzip z3-4.12.1-x64-ubuntu-20.04-bin.zip
	rm z3-4.12.1-x64-ubuntu-20.04-bin.zip
	wget https://github.com/dafny-lang/solver-builds/releases/download/snapshot-2023-08-02/z3-4.8.5-x64-ubuntu-20.04-bin.zip
	unzip z3-4.8.5-x64-ubuntu-20.04-bin.zip
	rm z3-4.8.5-x64-ubuntu-20.04-bin.zip
	mv z3-* "${DIR}"/Binaries/z3/bin/
	chmod +x "${DIR}"/Binaries/z3/bin/z3-*

format:
	dotnet format whitespace Source/Dafny.sln --exclude Source/DafnyCore/Scanner.cs --exclude Source/DafnyCore/Parser.cs --exclude boogie --exclude Source/DafnyCore/GeneratedFromDafny/* --exclude Source/DafnyCore.Test/GeneratedFromDafny/* --exclude Source/DafnyRuntime/DafnyRuntimeSystemModule.cs

clean:
	(cd "${DIR}"; cd Source; rm -rf Dafny/bin Dafny/obj DafnyDriver/bin DafnyDriver/obj DafnyRuntime/obj DafnyRuntime/bin DafnyServer/bin DafnyServer/obj DafnyPipeline/obj DafnyPipeline/bin DafnyCore/obj DafnyCore/bin)
	(cd "${DIR}" ; dotnet build Source/Dafny.sln -v:q --nologo -target:clean )
	make -C "${DIR}"/Source/DafnyCore -f Makefile clean
	(cd "${DIR}"/Source/Dafny && rm -rf Scanner.cs Parser.cs obj )
	(cd "${DIR}"/Source/DafnyRuntime/DafnyRuntimeJava; ./gradlew clean)
	make -C "${DIR}"/docs/DafnyRef clean
	(cd "${DIR}"; cd Source; rm -rf Dafny/bin Dafny/obj DafnyDriver/bin DafnyDriver/obj DafnyRuntime/obj DafnyRuntime/bin DafnyServer/bin DafnyServer/obj DafnyPipeline/obj DafnyPipeline/bin DafnyCore/obj DafnyCore/bin)
	echo Source/*/bin Source/*/obj

bumpversion-test:
	node ./Scripts/bump_version_number.js --test 1.2.3

update-cs-module:
	(cd "${DIR}"; cd Source/DafnyRuntime; make update-system-module)

update-rs-module:
	(cd "${DIR}"; cd Source/DafnyRuntime/DafnyRuntimeRust; make update-system-module)

update-go-module:
	(cd "${DIR}"; cd Source/DafnyRuntime/DafnyRuntimeGo; make update-system-module)

update-runtime-dafny:
	(cd "${DIR}"; cd Source/DafnyRuntime/DafnyRuntimeDafny; make update-go)

pr-nogeneration: format-dfy format update-runtime-dafny update-cs-module update-rs-module update-go-module

update-standard-libraries:
	(cd "${DIR}"; cd Source/DafnyStandardLibraries; make update-binary)

# `make pr` will bring you in a state suitable for submitting a PR
# - Builds the Dafny executable
# - Use the build to convert core .dfy files to .cs
# - Rebuilds the Dafny executable with this .cs files
# - Apply dafny format on all dfy files
# - Apply dotnet format on all cs files except the generated ones
# - Rebuild the Go and C# runtime modules as needed.
pr: exe dfy-to-cs-exe pr-nogeneration

# Same as `make pr` but useful when resolving conflicts, to take the last compiled version of Dafny first
pr-conflict: dfy-to-cs-exe dfy-to-cs-exe pr-nogeneration
