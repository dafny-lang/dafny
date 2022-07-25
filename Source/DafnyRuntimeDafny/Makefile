

verify:
	dafny /compile:0 /definiteAssignment:3 src/array.dfy

java: verify
	dafny /noVerify /compile:0 /spillTargetCode:3 /useRuntimeLib src/array.dfy /compileTarget:java /out:../DafnyRuntime/DafnyRuntimeJava/src/main/generated

cs: verify
	dafny /noVerify /compile:0 /spillTargetCode:3 /useRuntimeLib src/array.dfy /compileTarget:cs /out:../DafnyRuntime/generated

py: verify
	dafny /noVerify /compile:0 /spillTargetCode:3 /useRuntimeLib src/array.dfy /compileTarget:py /out:../DafnyRuntime/generated

build:
	dotnet build ../DafnyRuntime

all: verify cs java build
