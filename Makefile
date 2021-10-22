DIR=$(dir $(realpath $(firstword $(MAKEFILE_LIST))))

default: parser runtime boogie exe

all: runtime boogie exe refman

exe:
	(cd ${DIR} ; dotnet build Source/Dafny.sln ) ## includes parser

boogie: ${DIR}/Source/boogie/Binaries/Boogie.exe

${DIR}/Source/boogie/Binaries/Boogie.exe:
	(cd ${DIR}/../boogie ; dotnet build Source/boogie/Source/Boogie.sln )

parser:
	make -C ${DIR}/Source/Dafny -f Makefile.linux all

refman:
	make -C ${DIR}/docs/DafnyRef

refman-release:
	make -C ${DIR}/docs/DafnyRef release

z3-mac:
	wget https://github.com/Z3Prover/z3/releases/download/Z3-4.8.5/z3-4.8.5-x64-osx-10.14.2.zip
	unzip z3-4.8.5-x64-osx-10.14.2.zip
	mv z3-4.8.5-x64-osx-10.14.2 ${DIR}/Binaries/z3

z3-ubuntu:
	wget https://github.com/Z3Prover/z3/releases/download/Z3-4.8.5/z3-4.8.5-x64-ubuntu-16.04.zip
	unzip z3-4.8.5-x64-ubuntu-16.04.zip
	mv z3-4.8.5-x64-ubuntu-16.04 ${DIR}/Binaries/z3

clean:
	(cd ${DIR}; cd Source; rm -rf Dafny/bin Dafny/obj DafnyDriver/bin DafnyDriver/obj DafnyRuntime/obj DafnyRuntime/bin DafnyServer/bin DafnyServer/obj DafnyPipeline/obj DafnyPipeline/bin )
	(cd ${DIR} ; dotnet build Source/Dafny.sln -v:q --nologo -target:clean )
	make -C ${DIR}/Source/Dafny -f Makefile.Linux clean
	(cd ${DIR}/Source/DafnyRuntime/DafnyRuntimeJava; ./gradlew clean)
	make -C ${DIR}/docs/DafnyRef clean
	(cd ${DIR}; cd Source; rm -rf Dafny/bin Dafny/obj DafnyDriver/bin DafnyDriver/obj DafnyRuntime/obj DafnyRuntime/bin DafnyServer/bin DafnyServer/obj DafnyPipeline/obj DafnyPipeline/bin )
	echo Source/*/bin Source/*/obj
