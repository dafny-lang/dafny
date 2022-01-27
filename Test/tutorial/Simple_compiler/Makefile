DafnyDriver = ../../../Source/DafnyDriver/DafnyDriver

default: run

Compiler.cs: Compiler.dfy
	dotnet run --project $(DafnyDriver).csproj -- \
		/spillTargetCode:3 /compile:0 /noVerify $<

dll := bin/Debug/net6.0/SimpleCompiler.dll

$(dll): Main.cs Compiler.cs Simple.g4
	dotnet build

input := example_input.calc

run: $(dll) $(input)
	dotnet $^
