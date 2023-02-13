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
	wget https://github.com/Z3Prover/z3/releases/download/z3-4.12.1/z3-4.12.1-x64-osx-10.16.zip
	unzip z3-4.12.1-x64-osx-10.16.zip
	mv z3-4.12.1-x64-osx-10.16 ${DIR}/Binaries/z3
	rm z3-4.12.1-x64-osx-10.16.zip

z3-ubuntu:
	wget https://github.com/Z3Prover/z3/releases/download/z3-4.12.1/z3-4.12.1-x64-glibc-2.31.zip
	unzip z3-4.12.1-x64-glibc-2.31.zip
	mv z3-4.12.1-x64-glibc-2.31 ${DIR}/Binaries/z3
	rm z3-4.12.1-x64-glibc-2.31.zip

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
