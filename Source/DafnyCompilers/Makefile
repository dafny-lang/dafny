default: build

MAKEFLAGS += --no-builtin-rules
.SUFFIXES:

AutoExtern = ../AutoExtern
DafnyDriver = ../DafnyDriver/DafnyDriver
DafnyPipeline = ../Dafny/DafnyPipeline
DafnyAST = ../Dafny/AST/DafnyAst
DafnyRuntime := ../DafnyRuntime/DafnyRuntime.cs
ASTModel := CSharpDafnyASTModel.dfy
CompilerDLL := CSharp/bin/Debug/net6.0/CSharpCompiler.dll

dafny := dotnet run --project $(DafnyDriver).csproj --
dafny2cs := $(dafny) /spillTargetCode:3 /compile:0 /noVerify

# Model files contain traits that give type signatures of existing C# and Dafny/Boogie classes
dfy_models := $(AutoExtern)/CSharpModel.dfy CSharpDafnyModel.dfy CSharpDafnyASTModel.dfy

# Interop files contain Dafny functions implemented in C# that help interop with the models
dfy_interop := CSharpInterop.dfy CSharpDafnyInterop.dfy CSharpDafnyASTInterop.dfy
cs_interop := $(dfy_interop:.dfy=.cs)

# Auto-generate a model of DafnyAST.sc
$(ASTModel): $(DafnyPipeline).csproj $(DafnyAST).cs $(ASTModel).template $(AutoExtern)/Program.cs
	dotnet run --project $(AutoExtern)/AutoExtern.csproj -- \
		$(DafnyPipeline).csproj $(DafnyAST).cs "Microsoft.Dafny" "$(ASTModel).template" \
		"" "$@"

# Translate the compiler from Dafny to C#
CSharp/Compiler.cs: CSharp/Compiler.dfy CompilerCommon.dfy $(dfy_models) $(dfy_interop) $(DafnyRuntime)
	$(dafny2cs) $<
	sed -i.bak -e 's/__AUTOGEN__//g' "$@"
	rm "$@.bak" # https://stackoverflow.com/questions/4247068/

# Compile the resulting C# code
$(CompilerDLL): CSharp/Compiler.cs $(cs_interop)
	dotnet build CSharp/CSharpCompiler.csproj

# Run it
run: $(CompilerDLL) $(DafnyRuntime)
	dotnet run --project ../DafnyDriver/DafnyDriver.csproj -- \
		/plugin:$(CompilerDLL) /compileTarget:cs \
		/spillTargetCode:3 /compile:0 /noVerify \
		minimal.dfy

# Compile the REPL
# DISCUSS: Dependency tracking in Dafny
REPL/Repl.cs: REPL/Repl.dfy CompilerCommon.dfy $(ASTModel) $(dfy_models) $(dfy_interop) $(DafnyRuntime)
	$(dafny2cs) $<
	sed -i.bak -e 's/__AUTOGEN__//g' "$@"
	rm "$@.bak"

repl_dll := REPL/bin/Release/net6.0/Repl.dll

$(repl_dll): REPL/Repl.cs REPL/ReplInterop.cs $(cs_interop)
	dotnet build --configuration=Release REPL/REPL.csproj

FORCE:

# Run it
repl: $(repl_dll) FORCE
	dotnet exec $<

entry_points := REPL/Repl.dfy CSharp/Compiler.dfy

typecheck:
	$(dafny) -dafnyVerify:0 $(entry_points)

build: $(CompilerDLL)

clean:
	rm -f CSharp/Compiler.cs $(ASTModel)
