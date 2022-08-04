
all: verify cs java build

verify:
	dafny /compile:0 /definiteAssignment:3 src/dafnyRuntime.dfy

java: verify
	dafny /noVerify /compile:0 /spillTargetCode:3 /useRuntimeLib src/dafnyRuntime.dfy /compileTarget:java /out:../DafnyRuntime/DafnyRuntimeJava/src/main/generated

cs: verify
	dafny /noVerify /compile:0 /spillTargetCode:3 /useRuntimeLib src/dafnyRuntime.dfy /compileTarget:cs /out:../DafnyRuntime/generated

py: verify
	dafny /noVerify /compile:0 /spillTargetCode:3 /useRuntimeLib src/dafnyRuntime.dfy /compileTarget:py /out:../DafnyRuntime/generated
	
go: verify
    dafny /noVerify /compile:0 /spillTargetCode:3 /useRuntimeLib src/dafnyRuntime.dfy /compileTarget:go /out:../DafnyRuntime/generated

build:
	dotnet build ../DafnyRuntime
