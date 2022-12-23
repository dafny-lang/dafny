using System.Collections.Generic;
using System.CommandLine;
using System.IO;
using System.Linq;

namespace Microsoft.Dafny; 

public class CommonOptionBag {

  public static readonly Option<bool> ManualLemmaInduction =
    new("--manual-lemma-induction", "Turn off automatic induction for lemmas.");

  public static readonly Option<bool> OptimizeErasableDatatypeWrapper = new("--optimize-erasable-datatype-wrapper", () => true, @"
false - Include all non-ghost datatype constructors in the compiled code
true - In the compiled target code, transform any non-extern
    datatype with a single non-ghost constructor that has a single
    non-ghost parameter into just that parameter. For example, the type
        datatype Record = Record(x: int)
    is transformed into just 'int' in the target code.".TrimStart());

  public static readonly Option<bool> Verbose = new("--verbose",
    "Print additional information such as which files are emitted where.") {
  };

  public static readonly Option<bool> DisableNonLinearArithmetic = new("--disable-nonlinear-arithmetic",
    @"
(experimental, will be replaced in the future)
Reduce Dafny's knowledge of non-linear arithmetic (*,/,%).
  
Results in more manual work, but also produces more predictable behavior.".TrimStart()) {
  };

  public static readonly Option<bool> EnforceDeterminism = new("--enforce-determinism",
    "Check that only deterministic statements are used, so that values seen during execution will be the same in every run of the program.") {
  };

  public static readonly Option<bool> RelaxDefiniteAssignment = new("--relax-definite-assignment",
    "Allow variables to be read before they are assigned, but only if they have an auto-initializable type or if they are ghost and have a nonempty type.") {
  };

  public static readonly Option<IList<string>> Libraries = new("--library",
    @"
The contents of this file and any files it includes can be referenced from other files as if they were included. 
However, these contents are skipped during code generation and verification.
This option is useful in a diamond dependency situation, 
to prevent code from the bottom dependency from being generated more than once.".TrimStart());

  public static readonly Option<FileInfo> Output = new(new[] { "--output", "-o" },
    "Specify the filename and location for the generated target language files.") {
    ArgumentHelpName = "file"
  };

  public static readonly Option<IList<string>> Plugin = new(new[] { "--plugin" },
    @"
(experimental) One path to an assembly that contains at least one
instantiatable class extending Microsoft.Dafny.Plugin.Rewriter. It
can also extend Microsoft.Dafny.Plugins.PluginConfiguration to
receive arguments. More information about what plugins do and how
to define them:

https://github.com/dafny-lang/dafny/blob/master/Source/DafnyLanguageServer/README.md#about-plugins") {
    ArgumentHelpName = "path-to-one-assembly[,argument]*"
  };

  public static readonly Option<FileInfo> Prelude = new("--prelude", "Choose the Dafny prelude file.") {
    ArgumentHelpName = "file"
  };

  public static readonly Option<QuantifierSyntaxOptions> QuantifierSyntax = new("--quantifier-syntax",
    result => {
      if (result.Tokens.Any()) {
        var value = result.Tokens[0].Value;
        switch (value) {
          case "3": return QuantifierSyntaxOptions.Version3;
          case "4": return QuantifierSyntaxOptions.Version4;
          default:
            result.ErrorMessage = $"{value} is not a valid argument to {QuantifierSyntax.Name}";
            return default;
        }
      }

      return QuantifierSyntaxOptions.Version3;
    }, true, @"
The syntax for quantification domains is changing from Dafny version 3 to version 4, more specifically where quantifier ranges (|
<Range>) are allowed. This switch gives early access to the new syntax.

3 - Ranges are only allowed after all quantified variables are declared. 
    (e.g. set x, y | 0 <= x < |s| && y in s[x] && 0 <= y :: y)
4 - Ranges are allowed after each quantified variable declaration.
    (e.g. set x | 0 <= x < |s|, y <- s[x] | 0 <= y :: y)

Note that quantifier variable domains (<- <Domain>) are available in both syntax versions.".TrimStart()) {
    ArgumentHelpName = "version"
  };

  public static readonly Option<string> Target = new(new[] { "--target", "-t" }, () => "cs", @"
cs - Compile to .NET via C#.
go - Compile to Go.
js - Compile to JavaScript.
java - Compile to Java.
py - Compile to Python.
cpp - Compile to C++.

Note that the C++ backend has various limitations (see Docs/Compilation/Cpp.md). This includes lack of support for BigIntegers (aka int), most higher order functions, and advanced features like traits or co-inductive types.".TrimStart()
  ) {
    ArgumentHelpName = "language"
  };

  public static readonly Option<bool> UnicodeCharacters = new("--unicode-char", () => false,
    @"
false - The char type represents any UTF-16 code unit.
true - The char type represents any Unicode scalar value.".TrimStart());

  public static readonly Option<FileInfo> SolverPath = new("--solver-path",
    "Can be used to specify a custom SMT solver to use for verifying Dafny proofs.");
  public static readonly Option<bool> VerifyIncludedFiles = new("--verify-included-files",
    "Verify code in included files.");
  public static readonly Option<bool> WarningAsErrors = new("--warn-as-errors",
    "Treat warnings as errors.");
  public static readonly Option<bool> WarnMissingConstructorParenthesis = new("--warn-missing-constructor-parentheses",
    "Emits a warning when a constructor name in a case pattern is not followed by parentheses.");
  public static readonly Option<bool> WarnShadowing = new("--warn-shadowing",
    "Emits a warning if the name of a declared variable caused another variable to be shadowed.");

  public static readonly Option<bool> IncludeRuntime = new("--include-runtime",
    "Include the Dafny runtime as source in the target language.");

  public enum TestAssumptionsMode {
    None,
    Externs
  }

  public static readonly Option<TestAssumptionsMode> TestAssumptions = new("--test-assumptions", () => TestAssumptionsMode.None, @"
(experimental) When turned on, inserts runtime tests at locations where (implicit) assumptions occur, such as when calling or being called by external code and when using assume statements.

Functionality is still being expanded. Currently only checks contracts on every call to a function or method marked with the {:extern} attribute.".TrimStart());

  static CommonOptionBag() {
    QuantifierSyntax = QuantifierSyntax.FromAmong("3", "4");
    DafnyOptions.RegisterLegacyBinding(SolverPath, (options, value) => {
      if (value != null) {
        options.ProverOptions.Add($"PROVER_PATH={value?.FullName}");
      }
    });

    DafnyOptions.RegisterLegacyBinding(TestAssumptions, (options, value) => {
      options.TestContracts = value == TestAssumptionsMode.Externs ? DafnyOptions.ContractTestingMode.Externs : DafnyOptions.ContractTestingMode.None;
    });
    DafnyOptions.RegisterLegacyBinding(ManualLemmaInduction, (options, value) => {
      if (value) {
        options.Induction = 1;
      }
    });
    DafnyOptions.RegisterLegacyBinding(IncludeRuntime, (options, value) => { options.UseRuntimeLib = !value; });
    DafnyOptions.RegisterLegacyBinding(WarnShadowing, (options, value) => { options.WarnShadowing = value; });
    DafnyOptions.RegisterLegacyBinding(WarnMissingConstructorParenthesis,
      (options, value) => { options.DisallowConstructorCaseWithoutParentheses = value; });
    DafnyOptions.RegisterLegacyBinding(WarningAsErrors, (options, value) => { options.WarningsAsErrors = value; });
    DafnyOptions.RegisterLegacyBinding(VerifyIncludedFiles,
      (options, value) => { options.VerifyAllModules = value; });

    DafnyOptions.RegisterLegacyBinding(Target, (options, value) => { options.CompilerName = value; });


    DafnyOptions.RegisterLegacyBinding(QuantifierSyntax, (options, value) => { options.QuantifierSyntax = value; });

    DafnyOptions.RegisterLegacyBinding(Plugin, (options, value) => { options.AdditionalPluginArguments = value; });

    DafnyOptions.RegisterLegacyBinding(Prelude, (options, value) => {
      options.DafnyPrelude = value?.FullName;
      options.ExpandFilename(options.DafnyPrelude, x => options.DafnyPrelude = x, options.LogPrefix,
        options.FileTimestamp);
    });
    DafnyOptions.RegisterLegacyBinding(Libraries,
      (options, value) => { options.LibraryFiles = value.ToHashSet(); });
    DafnyOptions.RegisterLegacyBinding(Output, (options, value) => { options.DafnyPrintCompiledFile = value?.FullName; });

    DafnyOptions.RegisterLegacyBinding(Verbose, (o, v) => o.CompileVerbose = v);
    DafnyOptions.RegisterLegacyBinding(DisableNonLinearArithmetic, (o, v) => o.DisableNLarith = v);
    DafnyOptions.RegisterLegacyBinding(EnforceDeterminism, (options, value) => {
      options.ForbidNondeterminism = value;
      options.DefiniteAssignmentLevel = value ? 2 : 1;
    });
    RelaxDefiniteAssignment.AddValidator(optionResult => {
      var enforceDeterminismResult = optionResult.FindResultFor(EnforceDeterminism);
      if (enforceDeterminismResult is not null && enforceDeterminismResult.GetValueOrDefault<bool>()) {
        optionResult.ErrorMessage =
          $"The option {RelaxDefiniteAssignment.Name} can not be used in conjunction with {EnforceDeterminism.Name}.";
      }
    });
    DafnyOptions.RegisterLegacyBinding(RelaxDefiniteAssignment,
      (options, value) => { options.DefiniteAssignmentLevel = value ? 1 : 2; });

  }
}

