# Change this to `Dafny` to run with the system-wide Dafny
DAFNY_COMPILER ?= dotnet run --project ../../../Source/DafnyDriver/DafnyDriver.csproj

default: run

# Step 1: copy dependencies to `csharp` folder
csharp_dir := csharp
$(csharp_dir):
	mkdir "$@"
$(csharp_dir)/%: % | $(csharp_dir)
	cp "$<" "$@"

# Step 2: compile Dafny code, putting C# output in `csharp` folder
$(csharp_dir)/%.cs: %.dfy | $(csharp_dir)
	$(DAFNY_COMPILER) -spillTargetCode:3 -compile:0 "-out:$@" "$<"

# Step 3: compile resulting C# project
csproj := SimpleCompiler.csproj
csharp_deps := Main.cs Compiler.cs Simple.g4 $(csproj)
csharp_copied_deps := $(patsubst %,$(csharp_dir)/%,$(csharp_deps))
csharp_dll := $(csharp_dir)/bin/Debug/net6.0/SimpleCompiler.dll
$(csharp_dll): $(csharp_copied_deps)
	dotnet build $(csharp_dir)/$(csproj)

build: $(csharp_dll)

# Step 4: run example
input := example_input.calc
run: $(input) $(csharp_copied_deps)
	dotnet run --project $(csharp_dir)/$(csproj) -- $<

%.dfy.expect: %.dfy $(csharp_deps)
	$(MAKE) --quiet run > $@

clean:
	rm -fr $(csharp_dir) Compiler.dfy.expect
