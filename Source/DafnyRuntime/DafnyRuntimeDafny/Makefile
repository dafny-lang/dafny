

DAFNY_WITHOUT_RUNTIMES = dotnet run --project ../../DafnyDriver

all: verify cs java py js build

verify:
	$(DAFNY_WITHOUT_RUNTIMES) /compile:0 /definiteAssignment:3 src/dafnyRuntime.dfy

java: verify
	$(DAFNY_WITHOUT_RUNTIMES) /noVerify /compile:0 /spillTargetCode:3 /useRuntimeLib src/dafnyRuntime.dfy /compileTarget:java /out:../DafnyRuntimeJava/src/main/generated

cs: verify
	$(DAFNY_WITHOUT_RUNTIMES) /noVerify /compile:0 /spillTargetCode:3 /useRuntimeLib src/dafnyRuntime.dfy /compileTarget:cs /out:../generated

py: verify
	$(DAFNY_WITHOUT_RUNTIMES) /noVerify /compile:0 /spillTargetCode:3 /useRuntimeLib src/dafnyRuntime.dfy /compileTarget:py /out:../generated
	
go:
	$(DAFNY_WITHOUT_RUNTIMES) /noVerify /compile:0 /spillTargetCode:3 /useRuntimeLib src/dafnyRuntimeGo.dfy /compileTarget:go /out:../generated
	cp ../generated-go/src/dafny/dafny.go ../DafnyRuntimeGo/DafnyRuntimeFromDafny.go
# Probably the wrong place for this
	GO111MODULE=auto go test ../DafnyRuntimeGo

js: verify
	$(DAFNY_WITHOUT_RUNTIMES) /noVerify /compile:0 /spillTargetCode:3 /useRuntimeLib src/dafnyRuntime.dfy /compileTarget:js /out:../generated

build:
	dotnet build ../DafnyRuntime.csproj
