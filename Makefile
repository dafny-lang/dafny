DIR=$(dir $(realpath $(firstword $(MAKEFILE_LIST))))

default: exe

all: exe refman

exe:
	(cd ${DIR} ; dotnet build Source/Dafny.sln ) ## includes parser

boogie: ${DIR}/boogie/Binaries/Boogie.exe

tests:
	(cd ${DIR}; dotnet test Source/IntegrationTests)

tests-verbose:
	(cd ${DIR}; dotnet test --logger "console;verbosity=normal" Source/IntegrationTests )

${DIR}/boogie/Binaries/Boogie.exe:
	(cd ${DIR}/boogie ; dotnet build -c Release Source/Boogie.sln )

refman:
	make -C ${DIR}/docs/DafnyRef

refman-release:
	make -C ${DIR}/docs/DafnyRef release

z3-mac:
	mkdir -p ${DIR}Binaries/z3/bin
	wget https://github.com/dafny-lang/solver-builds/releases/download/snapshot-2023-02-17/z3-4.12.1-macos-11-bin.zip
	unzip z3-4.12.1-macos-11-bin.zip
	rm z3-4.12.1-macos-11-bin.zip
	wget https://github.com/dafny-lang/solver-builds/releases/download/snapshot-2023-02-17/z3-4.8.5-macos-11-bin.zip
	unzip z3-4.8.5-macos-11-bin.zip
	rm z3-4.8.5-macos-11-bin.zip
	mv z3-* ${DIR}/Binaries/z3/bin/
	chmod +x ${DIR}/Binaries/z3/bin/z3-*

z3-ubuntu:
	mkdir -p ${DIR}Binaries/z3/bin
	wget https://github.com/dafny-lang/solver-builds/releases/download/snapshot-2023-02-17/z3-4.12.1-ubuntu-20.04-bin.zip
	unzip z3-4.12.1-ubuntu-20.04-bin.zip
	rm z3-4.12.1-ubuntu-20.04-bin.zip
	wget https://github.com/dafny-lang/solver-builds/releases/download/snapshot-2023-02-17/z3-4.8.5-ubuntu-20.04-bin.zip
	unzip z3-4.8.5-ubuntu-20.04-bin.zip
	rm z3-4.8.5-ubuntu-20.04-bin.zip
	mv z3-* ${DIR}/Binaries/z3/bin/
	chmod +x ${DIR}/Binaries/z3/bin/z3-*

format:
	dotnet tool run dotnet-format -w -s error Source/Dafny.sln --exclude DafnyCore/Scanner.cs --exclude DafnyCore/Parser.cs

clean:
	(cd ${DIR}; cd Source; rm -rf Dafny/bin Dafny/obj DafnyDriver/bin DafnyDriver/obj DafnyRuntime/obj DafnyRuntime/bin DafnyServer/bin DafnyServer/obj DafnyPipeline/obj DafnyPipeline/bin DafnyCore/obj DafnyCore/bin)
	(cd ${DIR} ; dotnet build Source/Dafny.sln -v:q --nologo -target:clean )
	make -C ${DIR}/Source/DafnyCore -f Makefile clean
	(cd ${DIR}/Source/Dafny && rm -rf Scanner.cs Parser.cs obj )
	(cd ${DIR}/Source/DafnyRuntime/DafnyRuntimeJava; ./gradlew clean)
	make -C ${DIR}/docs/DafnyRef clean
	(cd ${DIR}; cd Source; rm -rf Dafny/bin Dafny/obj DafnyDriver/bin DafnyDriver/obj DafnyRuntime/obj DafnyRuntime/bin DafnyServer/bin DafnyServer/obj DafnyPipeline/obj DafnyPipeline/bin DafnyCore/obj DafnyCore/bin)
	echo Source/*/bin Source/*/obj
