using System.Collections.Generic;
using System.CommandLine;
using System.IO;
using System.Linq;
using Microsoft.Boogie;

namespace Microsoft.Dafny;

public class CommonOptionBag {

  public static readonly Option<int> ErrorLimit =
    new("--error-limit", () => 5, "Set the maximum number of errors to report (0 for unlimited).");

  public static readonly Option<bool> ManualLemmaInduction =
    new("--manual-lemma-induction", "Turn off automatic induction for lemmas.");

  public static readonly Option<bool> StdIn = new("--stdin", () => false,
    @"Read standard input and treat it as an input .dfy file.");

  public static readonly Option<bool> Check = new("--check", () => false, @"
Instead of formatting files, verify that all files are already
formatted through and return a non-zero exit code if it is not the case".TrimStart());

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

  public static readonly Option<bool> IsolateAssertions = new("--isolate-assertions", @"Verify each assertion in isolation.");

  public static readonly Option<List<string>> VerificationLogFormat = new("--log-format", $@"
Logs verification results using the given test result format. The currently supported formats are `trx`, `csv`, and `text`. These are: the XML-based format commonly used for test results for .NET languages, a custom CSV schema, and a textual format meant for human consumption. You can provide configuration using the same string format as when using the --logger option for dotnet test, such as: --format ""trx;LogFileName=<...>"");

The `trx` and `csv` formats automatically choose an output file name by default, and print the name of this file to the console. The `text` format prints its output to the console by default, but can send output to a file given the `LogFileName` option.

The `text` format also includes a more detailed breakdown of what assertions appear in each assertion batch. When combined with the {CommonOptionBag.IsolateAssertions.Name} option, it will provide approximate time and resource use costs for each assertion, allowing identification of especially expensive assertions.".TrimStart()) {
    ArgumentHelpName = "configuration"
  };

  public static readonly Option<uint> SolverResourceLimit = new("--resource-limit", @"Specify the maximum resource limit (rlimit) value to pass to Z3. Multiplied by 1000 before sending to Z3.");
  public static readonly Option<string> SolverPlugin = new("--solver-plugin",
    @"Dafny uses Boogie as part of its verification process. This option allows customising that part using a Boogie plugin. More information about Boogie can be found at https://github.com/boogie-org/boogie. Information on how to construct Boogie plugins can be found by looking at the code in https://github.com/boogie-org/boogie/blob/v2.16.3/Source/Provers/SMTLib/ProverUtil.cs#L316");

  public static readonly Option<string> SolverLog =
    new("--solver-log", @"Specify a file to use to log the SMT-Lib text sent to the solver.") {
      IsHidden = true
    };
  public static readonly Option<bool> JsonDiagnostics = new("--json-diagnostics", @"Deprecated. Return diagnostics in a JSON format.") {
    IsHidden = true
  };

  public static readonly Option<IList<string>> Libraries = new("--library",
    @"
The contents of this file and any files it includes can be referenced from other files as if they were included. 
However, these contents are skipped during code generation and verification.
This option is useful in a diamond dependency situation, 
to prevent code from the bottom dependency from being generated more than once.
The value may be a comma-separated list of files and folders.".TrimStart());

  public static readonly Option<FileInfo> Output = new(new[] { "--output", "-o" },
    "Specify the filename and location for the generated target language files.") {
    ArgumentHelpName = "file",
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
    ArgumentHelpName = "file",
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

      return QuantifierSyntaxOptions.Version4;
    }, true, @"
The syntax for quantification domains is changing from Dafny version 3 to version 4, more specifically where quantifier ranges (|
<Range>) are allowed. This switch gives early access to the new syntax.

3 - Ranges are only allowed after all quantified variables are declared. 
    (e.g. set x, y | 0 <= x < |s| && y in s[x] && 0 <= y :: y)
4 - Ranges are allowed after each quantified variable declaration.
    (e.g. set x | 0 <= x < |s|, y <- s[x] | 0 <= y :: y)

Note that quantifier variable domains (<- <Domain>) are available in both syntax versions.".TrimStart()) {
    ArgumentHelpName = "version",
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
    ArgumentHelpName = "language",
  };

  public static readonly Option<bool> UnicodeCharacters = new("--unicode-char", () => true,
    @"
false - The char type represents any UTF-16 code unit.
true - The char type represents any Unicode scalar value.".TrimStart()) {
  };

  public static readonly Option<bool> TypeSystemRefresh = new("--type-system-refresh", () => false,
    @"
false - The type-inference engine and supported types are those of Dafny 4.0.
true - Use an updated type-inference engine. Warning: This mode is under construction and probably won't work at this time.".TrimStart()) {
    IsHidden = true
  };

  public static readonly Option<FileInfo> SolverPath = new("--solver-path",
    "Can be used to specify a custom SMT solver to use for verifying Dafny proofs.") {
  };
  public static readonly Option<bool> VerifyIncludedFiles = new("--verify-included-files",
    "Verify code in included files.");
  public static readonly Option<bool> UseBaseFileName = new("--use-basename-for-filename",
    "When parsing use basename of file for tokens instead of the path supplied on the command line") {
  };
  public static readonly Option<bool> SpillTranslation = new("--spill-translation",
    @"In case the Dafny source code is translated to another language, emit that translation.") {
  };
  public static readonly Option<bool> WarningAsErrors = new("--warn-as-errors",
    "Treat warnings as errors.");
  public static readonly Option<bool> WarnMissingConstructorParenthesis = new("--warn-missing-constructor-parentheses",
    "Emits a warning when a constructor name in a case pattern is not followed by parentheses.");
  public static readonly Option<bool> WarnShadowing = new("--warn-shadowing",
    "Emits a warning if the name of a declared variable caused another variable to be shadowed.");

  public static readonly Option<bool> IncludeRuntimeOption = new("--include-runtime",
    "Include the Dafny runtime as source in the target language.");

  public static readonly Option<bool> UseJavadocLikeDocstringRewriterOption = new("--javadoclike-docstring-plugin",
    "Rewrite docstrings using a simple Javadoc-to-markdown converter"
  );

  public enum TestAssumptionsMode {
    None,
    Externs
  }

  public static readonly Option<TestAssumptionsMode> TestAssumptions = new("--test-assumptions", () => TestAssumptionsMode.None, @"
(experimental) When turned on, inserts runtime tests at locations where (implicit) assumptions occur, such as when calling or being called by external code and when using assume statements.

Functionality is still being expanded. Currently only checks contracts on every call to a function or method marked with the {:extern} attribute.".TrimStart());

  static CommonOptionBag() {
    QuantifierSyntax = QuantifierSyntax.FromAmong("3", "4");
    DafnyOptions.RegisterLegacyBinding(JsonDiagnostics, (options, value) => {
      if (value) {
        options.Printer = new DafnyJsonConsolePrinter(options);
        options.DiagnosticsFormat = DafnyOptions.DiagnosticsFormats.JSON;
      }
    });
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
    DafnyOptions.RegisterLegacyBinding(IncludeRuntimeOption, (options, value) => { options.IncludeRuntime = value; });
    DafnyOptions.RegisterLegacyBinding(UseBaseFileName, (o, f) => o.UseBaseNameForFileName = f);
    DafnyOptions.RegisterLegacyBinding(UseJavadocLikeDocstringRewriterOption,
      (options, value) => { options.UseJavadocLikeDocstringRewriter = value; });
    DafnyOptions.RegisterLegacyBinding(WarnShadowing, (options, value) => { options.WarnShadowing = value; });
    DafnyOptions.RegisterLegacyBinding(WarnMissingConstructorParenthesis,
      (options, value) => { options.DisallowConstructorCaseWithoutParentheses = value; });
    DafnyOptions.RegisterLegacyBinding(WarningAsErrors, (options, value) => { options.WarningsAsErrors = value; });
    DafnyOptions.RegisterLegacyBinding(ErrorLimit, (options, value) => { options.ErrorLimit = value; });
    DafnyOptions.RegisterLegacyBinding(VerifyIncludedFiles,
      (options, value) => { options.VerifyAllModules = value; });

    DafnyOptions.RegisterLegacyBinding(Target, (options, value) => { options.CompilerName = value; });


    DafnyOptions.RegisterLegacyBinding(QuantifierSyntax, (options, value) => { options.QuantifierSyntax = value; });

    DafnyOptions.RegisterLegacyBinding(Plugin, (options, value) => { options.AdditionalPluginArguments = value; });

    DafnyOptions.RegisterLegacyBinding(Check, (options, value) => {
      options.FormatCheck = value;
    });

    DafnyOptions.RegisterLegacyBinding(StdIn, (options, value) => {
      options.UseStdin = value;
    });

    DafnyOptions.RegisterLegacyBinding(FormatPrint, (options, value) => {
      options.DafnyPrintFile = value ? "-" : null;
    });

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

    DafnyOptions.RegisterLegacyBinding(VerificationLogFormat, (o, v) => o.VerificationLoggerConfigs = v);
    DafnyOptions.RegisterLegacyBinding(IsolateAssertions, (o, v) => o.VcsSplitOnEveryAssert = v);
    DafnyOptions.RegisterLegacyBinding(SolverResourceLimit, (o, v) => o.ResourceLimit = v);
    DafnyOptions.RegisterLegacyBinding(SolverPlugin, (o, v) => {
      if (v is not null) {
        o.ProverDllName = v;
        o.TheProverFactory = ProverFactory.Load(o.ProverDllName);
      }
    });
    DafnyOptions.RegisterLegacyBinding(SolverLog, (o, v) => o.ProverLogFilePath = v);
    DafnyOptions.RegisterLegacyBinding(SpillTranslation, (o, f) => o.SpillTargetCode = f ? 1U : 0U);

    DafnyOptions.RegisterLegacyBinding(EnforceDeterminism, (options, value) => {
      options.ForbidNondeterminism = value;
      options.DefiniteAssignmentLevel = 4;
    });
    RelaxDefiniteAssignment.AddValidator(optionResult => {
      var enforceDeterminismResult = optionResult.FindResultFor(EnforceDeterminism);
      if (enforceDeterminismResult is not null && enforceDeterminismResult.GetValueOrDefault<bool>()) {
        optionResult.ErrorMessage =
          $"The option {RelaxDefiniteAssignment.Name} can not be used in conjunction with {EnforceDeterminism.Name}.";
      }
    });
    DafnyOptions.RegisterLegacyBinding(RelaxDefiniteAssignment,
      (options, value) => {
        if (!options.Get(EnforceDeterminism)) {
          options.DefiniteAssignmentLevel = value ? 1 : 4;
        }
      });
  }


  public static readonly Option<bool> FormatPrint = new("--print",
    @"Print Dafny program to stdout after formatting it instead of altering the files.") {
  };
}

