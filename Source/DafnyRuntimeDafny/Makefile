

verify:
	dafny /compile:0 src/array.dfy

java:
	dafny /noVerify /compile:0 /spillTargetCode:3 /useRuntimeLib src/array.dfy /compileTarget:java /out:../DafnyRuntime/DafnyRuntimeJava/src/main/generated

cs:
	dafny /noVerify /compile:0 /spillTargetCode:3 /useRuntimeLib src/array.dfy /compileTarget:cs /out:../DafnyRuntime/generated

build:
	dotnet build ../DafnyRuntime

all: verify cs java build
