

# TODO: make work for all platforms
DAFNY = dafny

all: verify cs java py js build

verify:
	$(DAFNY) /compile:0 /definiteAssignment:3 src/dafnyRuntime.dfy

java: verify
	$(DAFNY) /noVerify /compile:0 /spillTargetCode:3 /useRuntimeLib src/dafnyRuntime.dfy /compileTarget:java /out:../DafnyRuntimeJava/src/main/generated

cs: verify
	$(DAFNY) /noVerify /compile:0 /spillTargetCode:3 /useRuntimeLib src/dafnyRuntimeCsharp.dfy /compileTarget:cs /out:../../generated

py: verify
	$(DAFNY) /noVerify /compile:0 /spillTargetCode:3 /useRuntimeLib src/dafnyRuntime.dfy /compileTarget:py /out:../generated
	
go: verify
	$(DAFNY) /noVerify /compile:0 /spillTargetCode:3 /useRuntimeLib src/dafnyRuntimeGo.dfy /compileTarget:go /out:../generated
	cp ../generated-go/src/dafny/dafny.go ../DafnyRuntimeGo/DafnyRuntimeFromDafny.go
# Probably the wrong place for this
	GO111MODULE=auto go test ../DafnyRuntimeGo

js: verify
	$(DAFNY) /noVerify /compile:0 /spillTargetCode:3 /useRuntimeLib src/dafnyRuntime.dfy /compileTarget:js /out:../generated

build:
	dotnet build ../DafnyRuntime.csproj
