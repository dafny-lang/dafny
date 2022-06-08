# Change this to `Dafny` to run with the system-wide Dafny
DAFNY_COMPILER ?= dotnet run --project ../../../Source/DafnyDriver/DafnyDriver.csproj

default: run

# Step 1: Copy shared dependencies
csharp_dir := csharp
shared_deps := Simple.g4
$(csharp_dir)/%: %
	cp "$<" "$@"

# Step 2: create `csharp/_dafny`
dafny_csharp_dir := $(csharp_dir)/dafny
$(dafny_csharp_dir):
	mkdir "$@"

# Step 2: compile Dafny code, putting C# output in `csharp/dafny`
dafny_files := $(wildcard *.dfy)
$(dafny_csharp_dir)/%.cs: %.dfy | $(dafny_csharp_dir)
	$(DAFNY_COMPILER) -spillTargetCode:3 -compile:0 "-out:$@" "$<"

# Step 3: compile resulting C# project
csproj := SimpleCompiler.csproj
csharp_dll := $(csharp_dir)/bin/Debug/net6.0/SimpleCompiler.dll
csharp_files :=  $(wildcard $(csharp_dir)/*)
csharp_shared_deps := $(patsubst %,$(csharp_dir)/%,$(shared_deps))
csharp_dafny_deps := $(patsubst %.dfy,$(dafny_csharp_dir)/%.cs,$(dafny_files))
csharp_deps := $(csharp_shared_deps) $(csharp_dafny_deps) $(csharp_files)
build: $(csharp_dll)
$(csharp_dll): $(csharp_deps)
	dotnet build $(csharp_dir)/$(csproj)

# Step 4: run example
input := example_input.calc
run: $(input) $(csharp_deps)
	dotnet run --project $(csharp_dir)/$(csproj) -- $<

%.dfy.expect: %.dfy $(csharp_copied_deps)
	$(MAKE) --quiet run > $@

clean:
	rm -fr $(dafny_csharp_dir) $(csharp_shared_deps) \
		$(csharp_dir)/bin $(csharp_dir)/obj Compiler.dfy.expect
