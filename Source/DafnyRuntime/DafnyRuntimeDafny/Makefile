
all: verify cs java py js build

verify:
	dafny /compile:0 /definiteAssignment:3 src/dafnyRuntime.dfy

java: verify
	dafny /noVerify /compile:0 /spillTargetCode:3 /useRuntimeLib src/dafnyRuntime.dfy /compileTarget:java /out:../DafnyRuntimeJava/src/main/generated

cs: verify
	dafny /noVerify /compile:0 /spillTargetCode:3 /useRuntimeLib src/dafnyRuntime.dfy /compileTarget:cs /out:../generated

py: verify
	dafny /noVerify /compile:0 /spillTargetCode:3 /useRuntimeLib src/dafnyRuntime.dfy /compileTarget:py /out:../generated
	
go: verify
	dafny /noVerify /compile:0 /spillTargetCode:3 /useRuntimeLib src/dafnyRuntimeGo.dfy /compileTarget:go /out:../generated

js: verify
	dafny /noVerify /compile:0 /spillTargetCode:3 /useRuntimeLib src/dafnyRuntime.dfy /compileTarget:js /out:../generated

build:
	dotnet build ../DafnyRuntime
