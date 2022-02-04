DafnyDriver = ../../../Source/DafnyDriver/DafnyDriver
deps := Main.cs Compiler.cs Simple.g4
dll := bin/Debug/net6.0/SimpleCompiler.dll
input := example_input.calc

default: run

Compiler.cs: Compiler.dfy
	dotnet run --project $(DafnyDriver).csproj -- \
		/spillTargetCode:3 /compile:0 /noVerify $<

$(dll): $(deps)
	dotnet build

build: $(dll)

run: $(input) $(deps)
	dotnet run -- $<
