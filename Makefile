DIR=$(dir $(realpath $(firstword $(MAKEFILE_LIST))))

default: parser runtime boogie exe

all: parser runtime boogie exe refman

exe: parser
	(cd ${DIR} ; dotnet build Source/Dafny.sln )

boogie: ${DIR}/../boogie/Binaries/Boogie.exe

${DIR}/../boogie/Binaries/Boogie.exe:
	(cd ${DIR}/../boogie ; msbuild Source/Boogie.sln )

parser:
	make -C ${DIR}/Source/Dafny -f Makefile.linux all

runtime: ${DIR}/Binaries/DafnyRuntime.jar

${DIR}/Binaries/DafnyRuntime.jar:
	(cd ${DIR}/Source/DafnyRuntime/DafnyRuntimeJava; ./gradlew copyJarToBinaries)

refman:
	make -C ${DIR}/docs/DafnyReferenceManual

clean:
	(cd ${DIR} ; msbuild Source/Dafny.sln -target:clean )
	make -C ${DIR}/Source/Dafny -f Makefile.Linux clean
	(cd ${DIR}/Source/DafnyRuntime/DafnyRuntimeJava; ./gradlew clean)
	make -C ${DIR}/docs/DafnyReferenceManual clean
