DIR=$(dir $(realpath $(firstword $(MAKEFILE_LIST))))

default: parser runtime boogie exe

all: parser runtime boogie exe refman

exe:
	(cd ${DIR} ; msbuild Source/Dafny.sln )

boogie: ${DIR}/../boogie/Binaries/Boogie.exe

${DIR}/../boogie/Binaries/Boogie.exe:
	(cd ${DIR}/../boogie ; msbuild Source/Boogie.sln )

parser: 
	make -C ${DIR}/Source/Dafny -f Makefile.linux all

runtime: ${DIR}/Binaries/DafnyRuntime.jar

${DIR}/Binaries/DafnyRuntime.jar:
	(cd ${DIR}/Source/DafnyRuntime/DafnyRuntimeJava; ./gradlew build && gradle copyJarToBinaries)

refman:
	make -C ${DIR}/docs/DafnyReferenceManual

clean:
	(cd ${DIR} ; rm -f Source/Dafny/bin/Debug/* Binaries/dafny.exe )
	make -C ${DIR}/Source/Dafny clean
	(cd ${DIR} ; rm -f Binaries/DafnyRuntime.jar )
	(cd ${DIR} ; rm -f docs/DafnyReferenceManual/DafnyRef.pdf )
