using System;
using System.Collections.Generic;
using System.CommandLine;
using System.IO;
using System.Linq;
using DafnyCore;
using DafnyCore.Options;
using Serilog.Events;
using Microsoft.Dafny.Compilers;

namespace Microsoft.Dafny;

public class CommonOptionBag {

  public static void EnsureStaticConstructorHasRun() { }

  public static readonly Option<bool> CheckSourceLocationConsistency =
    new("--check-source-location-consistency", "Check that parent nodes contain their children") {
      IsHidden = true
    };

  public enum ProgressLevel { None, Symbol, Batch }
  public static readonly Option<ProgressLevel> ProgressOption =
    new("--progress", $"While verifying, output information that helps track progress. " +
                      $"Use '{ProgressLevel.Symbol}' to show progress across symbols such as methods and functions. " +
                      $"Verification of a symbol may be split across several assertion batches. " +
                      $"Use {ProgressLevel.Batch} to additionally show progress across batches.");

  public static readonly Option<bool> IgnoreIndentation =
    new("--ignore-indentation", "Do not report warnings for suspicious indentation") {
      IsHidden = true
    };

  public static readonly Option<bool> WaitForDebugger =
    new("--wait-for-debugger", "Lets the C# compiler block until a .NET debugger is attached") {
      IsHidden = true
    };

  public static readonly Option<bool> PrintDiagnosticsRanges =
    new("--print-ranges", "Prints not just the center, but also the start and end of diagnostics") {
      IsHidden = true
    };

  public static readonly Option<string> LogLocation =
    new("--log-location", "Sets the directory where to store log files") {
      IsHidden = true
    };

  public static readonly Option<LogEventLevel> LogLevelOption =
    new("--log-level", () => LogEventLevel.Error, "Sets the level at which events are logged") {
      IsHidden = true
    };

  public static readonly Option<bool> ManualTriggerOption =
    new("--manual-triggers", "Do not generate {:trigger} annotations for user-level quantifiers") {
      IsHidden = true
    };

  public static readonly Option<bool> ShowHints =
    new("--show-hints", () => false, "Show hints that might help you better understand your code, such as what triggers Dafny generators for quantifiers") {
      IsHidden = true
    };

  public enum AssertionShowMode { None, Implicit, All }
  public static readonly Option<AssertionShowMode> ShowAssertions = new("--show-assertions", () => AssertionShowMode.None,
    "Show hints on locations where implicit assertions occur");

  public static readonly Option<bool> AddCompileSuffix =
    new("--compile-suffix", "Add the suffix _Compile to module names without :extern") {
      IsHidden = true
    };

  public static readonly Option<bool> ManualLemmaInduction =
    new("--manual-lemma-induction", "Turn off automatic induction for lemmas.");

  public static readonly Option<bool> StdIn = new("--stdin", () => false,
    @"Read standard input and treat it as an input .dfy file.");

  public static readonly Option<bool> OptimizeErasableDatatypeWrapper = new("--optimize-erasable-datatype-wrapper", () => true, @"
false - Include all non-ghost datatype constructors in the compiled code
true - In the compiled target code, transform any non-extern
    datatype with a single non-ghost constructor that has a single
    non-ghost parameter into just that parameter. For example, the type
        datatype Record = Record(x: int)
    is transformed into just 'int' in the target code.".TrimStart());

  public static readonly Option<bool> Verbose = new("--verbose",
      "Print additional information such as which files are emitted where.");

  public static readonly Option<bool> AllowDeprecation = new("--allow-deprecation",
    "Do not warn about the use of deprecated features.") {
  };

  public static readonly Option<bool> DisableNonLinearArithmetic = new("--disable-nonlinear-arithmetic",
    @"
(experimental, will be replaced in the future)
Reduce Dafny's knowledge of non-linear arithmetic (*,/,%).
  
Results in more manual work, but also produces more predictable behavior.".TrimStart());

  public static readonly Option<bool> EnforceDeterminism = new("--enforce-determinism",
    "Check that only deterministic statements are used, so that values seen during execution will be the same in every run of the program.") {
  };

  public static readonly Option<bool> RelaxDefiniteAssignment = new("--relax-definite-assignment",
    "Allow variables to be read before they are assigned, but only if they have an auto-initializable type or if they are ghost and have a nonempty type.") {
  };

  public static readonly Option<IList<string>> VerificationLogFormat = new("--log-format", $@"
Logs verification results using the given test result format. The currently supported formats are `trx`, `csv`, and `text`. These are: the XML-based format commonly used for test results for .NET languages, a custom CSV schema, and a textual format meant for human consumption. You can provide configuration using the same string format as when using the --logger option for dotnet test, such as: --format ""trx;LogFileName=<...>"");

The `trx` and `csv` formats automatically choose an output file name by default, and print the name of this file to the console. The `text` format prints its output to the console by default, but can send output to a file given the `LogFileName` option.

The `text` format also includes a more detailed breakdown of what assertions appear in each assertion batch. When combined with the {BoogieOptionBag.IsolateAssertions.Name} option, it will provide approximate time and resource use costs for each assertion, allowing identification of especially expensive assertions.".TrimStart()) {
    ArgumentHelpName = "configuration"
  };

  public static readonly Option<bool> JsonDiagnostics = new("--json-diagnostics", @"Deprecated. Return diagnostics in a JSON format.") {
    IsHidden = true
  };
  public static readonly Option<bool> JsonOutput = new("--json-output", @"Return output in a JSON format.");

  public static readonly Option<IList<FileInfo>> Libraries = new("--library", () => new List<FileInfo>(),
    @"
The contents of this file and any files it includes can be referenced from other files as if they were included. 
However, these contents are skipped during code generation and verification.
This option is useful in a diamond dependency situation, 
to prevent code from the bottom dependency from being generated more than once.
The value may be a comma-separated list of files and folders.".TrimStart());

  public static IEnumerable<string> SplitOptionValueIntoFiles(IEnumerable<string> inputs) {
    var result = new HashSet<string>();
    foreach (var input in inputs) {
      var values = input.Split(',');
      foreach (var slice in values) {
        var name = slice.Trim();
        if (Directory.Exists(name)) {
          var files = Directory.GetFiles(name, "*.dfy", SearchOption.AllDirectories);
          foreach (var file in files) { result.Add(file); }
        } else {
          result.Add(name);
        }
      }
    }
    return result;
  }

  public static readonly Option<FileInfo> BuildFile = new(["--build", "-b"],
    "Specify the filepath that determines where to place and how to name build files.") {
    ArgumentHelpName = "file",
    IsHidden = true
  };

  public static readonly Option<FileInfo> Output = new(["--output", "-o"],
    "Specify the filename and location for the generated target language files.") {
    ArgumentHelpName = "file",
  };

  public static readonly Option<IList<string>> PluginOption = new(["--plugin"],
    @"
(experimental) One path to an assembly that contains at least one
instantiatable class extending Microsoft.Dafny.Plugin.Rewriter. It
can also extend Microsoft.Dafny.Plugins.PluginConfiguration to
receive arguments. More information about what plugins do and how
to define them:

https://github.com/dafny-lang/dafny/blob/master/Source/DafnyLanguageServer/README.md#about-plugins") {
    ArgumentHelpName = "path-to-one-assembly[,argument]*",
    IsHidden = true
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

  public static readonly Option<string> Target = new(["--target", "-t"], () => "cs", @"
cs - Compile to .NET via C#.
go - Compile to Go.
js - Compile to JavaScript.
java - Compile to Java.
py - Compile to Python.
cpp - (experimental) Compile to C++.

Note that the C++ backend has various limitations (see Docs/Compilation/Cpp.md). This includes lack of support for BigIntegers (aka int), most higher order functions, and advanced features like traits or co-inductive types.".TrimStart()
  ) {
    ArgumentHelpName = "language",
  };

  public static readonly Option<bool> UnicodeCharacters = new("--unicode-char", () => true,
    @"
false - The char type represents any UTF-16 code unit.
true - The char type represents any Unicode scalar value.".TrimStart()) {
    IsHidden = true
  };

  public static readonly Option<bool> RawPointers = new("--raw-pointers", () => false,
    @"(backend-specific: Rust)
false - All class instances are reference-counted or garbage collected
true - All class instances are raw pointers and need to be manually deallocated") {
    IsHidden = true
  };

  public static readonly Option<bool> AllowAxioms = new("--allow-axioms", () => false,
    "Prevents a warning from being generated for axioms, such as assume statements and functions or methods without a body, that don't have an {:axiom} attribute.") {
  };

  public static readonly Option<bool> TypeSystemRefresh = new("--type-system-refresh", () => false,
    @"
false - The type-inference engine and supported types are those of Dafny 4.0.
true - Use an updated type-inference engine.".TrimStart()) {
    IsHidden = true
  };

  public enum GeneralTraitsOptions {
    Legacy,
    Datatype,
    Full
  }

  public static readonly Option<GeneralTraitsOptions> GeneralTraits = new("--general-traits", () => GeneralTraitsOptions.Legacy,
    @"
legacy (default) - Every trait implicitly extends 'object', and thus is a reference type. Only traits and reference types can extend traits.
datatype - A trait is a reference type only if it or one of its ancestor traits is 'object'. Any non-'newtype' type with members can extend traits.
full - (don't use; not yet completely supported) A trait is a reference type only if it or one of its ancestor traits is 'object'. Any type with members can extend traits.".TrimStart()) {
    IsHidden = true
  };

  public static readonly Option<bool> GeneralNewtypes = new("--general-newtypes", () => false,
    @"
false - A newtype can only be based on numeric types or another newtype.
true - (requires --type-system-refresh) A newtype case be based on any non-reference, non-trait, non-arrow, non-ORDINAL type.".TrimStart()) {
    IsHidden = true
  };

  public static readonly Option<bool> TypeInferenceDebug = new("--type-inference-trace", () => false,
    @"
false - Don't print type-inference debug information.
true - Print type-inference debug information.".TrimStart()) {
    IsHidden = true
  };

  public static readonly Option<bool> NewTypeInferenceDebug = new("--type-system-debug", () => false,
    @"
false - Don't print debug information for the new type system.
true - Print debug information for the new type system.".TrimStart()) {
    IsHidden = true
  };

  public static readonly Option<bool> VerifyIncludedFiles = new("--verify-included-files",
    "Verify code in included files.");
  public static readonly Option<bool> UseBaseFileName = new("--use-basename-for-filename",
    "When parsing use basename of file for tokens instead of the path supplied on the command line") {
  };
  public static readonly Option<bool> EmitUncompilableCode = new("--emit-uncompilable-code",
    "Rather than throwing an exception, allow compilers to emit uncompilable information including what is " +
    "not compilable instead of regular code. Useful when developing compilers or to document for each test what " +
    "compiler feature is missing") {
  };
  public static readonly Option<bool> Referrers = new("--referrers", () => false,
    "Enables the modeling of backreferences in Dafny, so that one can reason about memory locations at " +
    "which objects are being stored.") {
    IsHidden = true
  };
  public static readonly Option<bool> SpillTranslation = new("--spill-translation",
    @"In case the Dafny source code is translated to another language, emit that translation.") {
  };

  public static readonly Option<bool> WarnAsErrors = new("--warn-as-errors", () => true, "(Deprecated). Please use --allow-warnings instead") {
    IsHidden = true
  };

  public enum InputTypeEnum {
    Source,
    Binary
  }

  public static readonly Option<InputTypeEnum> InputType = new("--input-format", () => InputTypeEnum.Source) {
    IsHidden = true
  };

  public static readonly Option<bool> AllowWarnings = new("--allow-warnings",
    "Allow compilation to continue and succeed when warnings occur. Errors will still halt and fail compilation.");

  public static readonly Option<bool> WarnMissingConstructorParenthesis = new("--warn-missing-constructor-parentheses",
    "Emits a warning when a constructor name in a case pattern is not followed by parentheses.");
  public static readonly Option<bool> WarnShadowing = new("--warn-shadowing",
    "Emits a warning if the name of a declared variable caused another variable to be shadowed.");
  public static readonly Option<bool> WarnContradictoryAssumptions = new("--warn-contradictory-assumptions", @"
(experimental) Emits a warning if any assertions are proved based on contradictory assumptions (vacuously).
May slow down verification slightly, or make it more brittle.
May produce spurious warnings.
Use the `{:contradiction}` attribute to mark any `assert` statement intended to be part of a proof by contradiction.") {
    IsHidden = true
  };
  public static readonly Option<bool> WarnRedundantAssumptions = new("--warn-redundant-assumptions", @"
(experimental) Emits a warning if any `requires` clause or `assume` statement was not needed to complete verification.
May slow down verification slightly, or make it more brittle.
May produce spurious warnings.") {
    IsHidden = true
  };
  public static readonly Option<bool> SuggestProofRefactoring = new("--suggest-proof-refactoring", @"
(experimental) Emits suggestions for moving assertions into by-proofs and hiding unused function definitions.
May produce spurious suggestions. Use with --show-hints on the CLI.") {
    IsHidden = true
  };
  public static readonly Option<bool> AnalyzeProofs = new("--analyze-proofs", @"
Uses data from the verifier to suggest ways to refine the proof:
Warning if any assertions are proved based on contradictory assumptions (vacuously).
Warning if any `requires` clause or `assume` statement was not needed to complete verification.
Suggestions for moving assertions into by-proofs and hiding unused function definitions.
May slow down verification slightly, or make it more brittle.
May produce spurious warnings.
Use the `{:contradiction}` attribute to mark any `assert` statement intended to be part of a proof by contradiction.
");
  public static readonly Option<string> VerificationCoverageReport = new("--verification-coverage-report",
    "Emit verification coverage report to a given directory, in the same format as a test coverage report.") {
    ArgumentHelpName = "directory"
  };
  public static readonly Option<bool> NoTimeStampForCoverageReport = new("--no-timestamp-for-coverage-report",
    "Write coverage report directly to the specified folder instead of creating a timestamped subdirectory.") {
    IsHidden = true
  };
  public static readonly Option<string> ExecutionCoverageReport = new("--coverage-report",
    "Emit execution coverage report to a given directory.") {
    ArgumentHelpName = "directory"
  };

  public static readonly Option<bool> IncludeRuntimeOption = new("--include-runtime",
    "Include the Dafny runtime as source in the target language.");

  /// <summary>
  /// Copy of --include-runtime for execution commands like `dafny run`,
  /// just so it can be internal only in that context:
  /// it shouldn't matter to end users but is useful for testing.
  /// </summary>
  public static readonly Option<bool> InternalIncludeRuntimeOptionForExecution = new("--include-runtime", () => true,
    "Include the Dafny runtime as source in the target language.") {
    IsHidden = true
  };

  public enum SystemModuleMode {
    Include,
    Omit,
    // Used to pre-compile the System module into the runtimes
    OmitAllOtherModules
  }

  public static readonly Option<SystemModuleMode> SystemModule = new("--system-module", () => SystemModuleMode.Omit,
    "How to handle the built-in _System module.") {
    IsHidden = true
  };

  public enum TestAssumptionsMode {
    None,
    Externs
  }

  public static readonly Option<TestAssumptionsMode> TestAssumptions = new("--test-assumptions", () => TestAssumptionsMode.None, @"
(experimental) When turned on, inserts runtime tests at locations where (implicit) assumptions occur, such as when calling or being called by external code and when using assume statements.

Functionality is still being expanded. Currently only checks contracts on every call to a function or method marked with the {:extern} attribute.".TrimStart());

  public enum DefaultFunctionOpacityOptions {
    Transparent,
    AutoRevealDependencies,
    Opaque
  }

  public static readonly Option<DefaultFunctionOpacityOptions> DefaultFunctionOpacity = new("--default-function-opacity", () => DefaultFunctionOpacityOptions.Transparent,
    @"
Change the default opacity of functions. 
`transparent` (default) means functions are transparent, can be manually made opaque and then revealed. 
`autoRevealDependencies` makes all functions not explicitly labelled as opaque to be opaque but reveals them automatically in scopes which do not have `{:autoRevealDependencies false}`. 
`opaque` means functions are always opaque so the opaque keyword is not needed, and functions must be revealed everywhere needed for a proof.".TrimStart()) {
  };

  public static readonly Option<bool> TranslateStandardLibrary = new("--translate-standard-library", () => true,
    @"When translating Dafny code to another language, Dafny will, for now, include the standard library as if these were source files. This causes conflicts when multiple such translated projects are combined. When combining such projects, please ensure that only one of them has --translate-standard-library set to true.
");

  public static readonly Option<bool> UseStandardLibraries = new("--standard-libraries", () => false,
    @"
Allow Dafny code to depend on the standard libraries included with the Dafny distribution.
See https://github.com/dafny-lang/dafny/blob/master/Source/DafnyStandardLibraries/README.md for more information.
Not compatible with the --unicode-char:false option.
");

  public static readonly Option<bool> ExtractCounterexample = new("--extract-counterexample", () => false,
    @"
If verification fails, report a detailed counterexample for the first failing assertion (experimental).".TrimStart()) {
  };

  public static readonly Option<bool> ShowProofObligationExpressions = new("--show-proof-obligation-expressions", () => false,
    @"
(Experimental) Show Dafny expressions corresponding to unverified proof obligations.".TrimStart()) {
    IsHidden = true
  };

  static CommonOptionBag() {
    DafnyOptions.RegisterLegacyBinding(WarnAsErrors, (options, value) => {
      if (!options.Get(AllowWarnings) && !options.Get(WarnAsErrors)) {
        // If allow warnings is at the default value, and warn-as-errors is not, use the warn-as-errors value
        options.Set(AllowWarnings, true);
        options.FailOnWarnings = false;
      }
    });

    DafnyOptions.RegisterLegacyUi(AllowAxioms, DafnyOptions.ParseBoolean, "Verification options", legacyName: "allowAxioms", defaultValue: true);
    DafnyOptions.RegisterLegacyBinding(ShowHints, (options, value) => {
      options.PrintTooltips = value;
    });

    DafnyOptions.RegisterLegacyBinding(ManualTriggerOption, (options, value) => {
      options.AutoTriggers = !value;
    });

    DafnyOptions.RegisterLegacyUi(Target, DafnyOptions.ParseString, "Compilation options", "compileTarget", @"
cs (default) - Compile to .NET via C#.
go - Compile to Go.
js - Compile to JavaScript.
java - Compile to Java.
py - Compile to Python.
cpp - Compile to C++.
dfy - Compile to Dafny.

Note that the C++ backend has various limitations (see
Docs/Compilation/Cpp.md). This includes lack of support for
BigIntegers (aka int), most higher order functions, and advanced
features like traits or co-inductive types.".TrimStart(), "cs");

    DafnyOptions.RegisterLegacyUi(OptimizeErasableDatatypeWrapper, DafnyOptions.ParseBoolean, "Compilation options", "optimizeErasableDatatypeWrapper", @"
0 - Include all non-ghost datatype constructors in the compiled code
1 (default) - In the compiled target code, transform any non-extern
    datatype with a single non-ghost constructor that has a single
    non-ghost parameter into just that parameter. For example, the type
        datatype Record = Record(x: int)
    is transformed into just 'int' in the target code.".TrimStart(), defaultValue: true);

    DafnyOptions.RegisterLegacyUi(VerificationLogFormat, DafnyOptions.ParseStringElement, "Verification options", "verificationLogger");
    DafnyOptions.RegisterLegacyUi(Output, DafnyOptions.ParseFileInfo, "Compilation options", "out");
    DafnyOptions.RegisterLegacyUi(UnicodeCharacters, DafnyOptions.ParseBoolean, "Language feature selection", "unicodeChar", @"
0 - The char type represents any UTF-16 code unit.
1 (default) - The char type represents any Unicode scalar value.".TrimStart(), defaultValue: true);
    DafnyOptions.RegisterLegacyUi(TypeSystemRefresh, DafnyOptions.ParseBoolean, "Language feature selection", "typeSystemRefresh", @"
0 (default) - The type-inference engine and supported types are those of Dafny 4.0.
1 - Use an updated type-inference engine.".TrimStart(), defaultValue: false);
    DafnyOptions.RegisterLegacyUi(GeneralTraits, DafnyOptions.ParseGeneralTraitsOption, "Language feature selection", "generalTraits", @"
legacy (default) - Every trait implicitly extends 'object', and thus is a reference type. Only traits and reference types can extend traits.
datatype - A trait is a reference type only if it or one of its ancestor traits is 'object'. Any non-'newtype' type with members can extend traits.
full - (don't use; not yet completely supported) A trait is a reference type only if it or one of its ancestor traits is 'object'. Any type with members can extend traits.".TrimStart(),
      defaultValue: GeneralTraitsOptions.Legacy);
    DafnyOptions.RegisterLegacyUi(GeneralNewtypes, DafnyOptions.ParseBoolean, "Language feature selection", "generalNewtypes", @"
0 (default) - A newtype can only be based on numeric types or another newtype.
1 - (requires /typeSystemRefresh:1) A newtype case be based on any non-reference, non-trait, non-arrow, non-ORDINAL type.".TrimStart(), false);
    DafnyOptions.RegisterLegacyUi(TypeInferenceDebug, DafnyOptions.ParseBoolean, "Language feature selection", "titrace", @"
0 (default) - Don't print type-inference debug information.
1 - Print type-inference debug information.".TrimStart(), defaultValue: false);
    DafnyOptions.RegisterLegacyUi(NewTypeInferenceDebug, DafnyOptions.ParseBoolean, "Language feature selection", "ntitrace", @"
0 (default) - Don't print debug information for the new type system.
1 - Print debug information for the new type system.".TrimStart(), defaultValue: false);
    DafnyOptions.RegisterLegacyUi(UseStandardLibraries, DafnyOptions.ParseBoolean, "Language feature selection", "standardLibraries", @"
0 (default) - Do not allow Dafny code to depend on the standard libraries included with the Dafny distribution.
1 - Allow Dafny code to depend on the standard libraries included with the Dafny distribution.
See https://github.com/dafny-lang/dafny/blob/master/Source/DafnyStandardLibraries/README.md for more information.
Not compatible with the /unicodeChar:0 option.".TrimStart(), defaultValue: false);
    DafnyOptions.RegisterLegacyUi(PluginOption, DafnyOptions.ParseStringElement, "Plugins", defaultValue: new List<string>());
    DafnyOptions.RegisterLegacyUi(Prelude, DafnyOptions.ParseFileInfo, "Input configuration", "dprelude");

    DafnyOptions.RegisterLegacyUi(Libraries, DafnyOptions.ParseFileInfoElement, "Compilation options", defaultValue: new List<FileInfo>());
    DafnyOptions.RegisterLegacyUi(DeveloperOptionBag.ResolvedPrint, DafnyOptions.ParseString, "Overall reporting and printing", "rprint");
    DafnyOptions.RegisterLegacyUi(DeveloperOptionBag.PrintOption, DafnyOptions.ParseString, "Overall reporting and printing", "dprint");

    DafnyOptions.RegisterLegacyUi(Snippets.ShowSnippets, DafnyOptions.ParseBoolean, "Overall reporting and printing", "showSnippets", @"
0 (default) - Don't show source code snippets for Dafny messages.
1 - Show a source code snippet for each Dafny message.".TrimStart());

    DafnyOptions.RegisterLegacyUi(Printer.PrintMode, ParsePrintMode, "Overall reporting and printing", "printMode", legacyDescription: @"
Everything (default) - Print everything listed below.
DllEmbed - print the source that will be included in a compiled dll.
NoIncludes - disable printing of {:verify false} methods
    incorporated via the include mechanism, as well as datatypes and
    fields included from other files.
NoGhost - disable printing of functions, ghost methods, and proof
    statements in implementation methods. It also disables anything
    NoIncludes disables.".TrimStart(),
      argumentName: "Everything|DllEmbed|NoIncludes|NoGhost",
      defaultValue: PrintModes.Everything);

    DafnyOptions.RegisterLegacyUi(DefaultFunctionOpacity, DafnyOptions.ParseDefaultFunctionOpacity, "Language feature selection", "defaultFunctionOpacity", null);

    DafnyOptions.RegisterLegacyUi(WarnContradictoryAssumptions, DafnyOptions.ParseImplicitEnable, "Verification options", "warnContradictoryAssumptions");
    DafnyOptions.RegisterLegacyUi(WarnRedundantAssumptions, DafnyOptions.ParseImplicitEnable, "Verification options", "warnRedundantAssumptions");
    DafnyOptions.RegisterLegacyUi(SuggestProofRefactoring, DafnyOptions.ParseImplicitEnable, "Verification options", "suggestProofRefactoring");

    void ParsePrintMode(Option<PrintModes> option, Boogie.CommandLineParseState ps, DafnyOptions options) {
      if (ps.ConfirmArgumentCount(1)) {
        if (ps.args[ps.i].Equals("Everything")) {
          options.Set(option, PrintModes.Everything);
        } else if (ps.args[ps.i].Equals("NoIncludes")) {
          options.Set(option, PrintModes.NoIncludes);
        } else if (ps.args[ps.i].Equals("NoGhost")) {
          options.Set(option, PrintModes.NoGhostOrIncludes);
        } else if (ps.args[ps.i].Equals("DllEmbed")) {
          // This is called DllEmbed because it was previously only used inside Dafny-compiled .dll files for C#,
          // but it is now used by the LibraryBackend when building .doo files as well. 
          options.Set(option, PrintModes.Serialization);
        } else {
          DafnyOptions.InvalidArgumentError(option.Name, ps);
        }
      }
    }

    DafnyOptions.RegisterLegacyUi(AddCompileSuffix, DafnyOptions.ParseBoolean, "Compilation options", "compileSuffix");

    QuantifierSyntax = QuantifierSyntax.FromAmong("3", "4");
    DafnyOptions.RegisterLegacyBinding(JsonDiagnostics, (options, value) => {
      if (value) {
        options.Printer = new DafnyJsonConsolePrinter(options);
        options.DiagnosticsFormat = DafnyOptions.DiagnosticsFormats.JSON;
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
    DafnyOptions.RegisterLegacyBinding(InternalIncludeRuntimeOptionForExecution, (options, value) => { options.IncludeRuntime = value; });
    DafnyOptions.RegisterLegacyBinding(SystemModule, (options, value) => { options.SystemModuleTranslationMode = value; });
    DafnyOptions.RegisterLegacyBinding(UseBaseFileName, (o, f) => o.UseBaseNameForFileName = f);
    DafnyOptions.RegisterLegacyBinding(WarnShadowing, (options, value) => { options.WarnShadowing = value; });
    DafnyOptions.RegisterLegacyBinding(WarnMissingConstructorParenthesis,
      (options, value) => { options.DisallowConstructorCaseWithoutParentheses = value; });
    DafnyOptions.RegisterLegacyBinding(AllowWarnings, (options, value) => { options.FailOnWarnings = !value; });
    DafnyOptions.RegisterLegacyBinding(VerifyIncludedFiles,
      (options, value) => { options.VerifyAllModules = value; });
    DafnyOptions.RegisterLegacyBinding(WarnContradictoryAssumptions, (options, value) => {
      if (value) { options.TrackVerificationCoverage = true; }
    });
    DafnyOptions.RegisterLegacyBinding(WarnRedundantAssumptions, (options, value) => {
      if (value) { options.TrackVerificationCoverage = true; }
    });
    DafnyOptions.RegisterLegacyBinding(SuggestProofRefactoring, (options, value) => {
      if (value) { options.TrackVerificationCoverage = true; }
    });
    DafnyOptions.RegisterLegacyBinding(AnalyzeProofs, (options, value) => {
      if (value) { options.TrackVerificationCoverage = true; }
    });

    DafnyOptions.RegisterLegacyBinding(Target, (options, value) => { options.CompilerName = value; });

    DafnyOptions.RegisterLegacyBinding(QuantifierSyntax, (options, value) => { options.QuantifierSyntax = value; });

    DafnyOptions.RegisterLegacyBinding(PluginOption, (options, value) => { options.AdditionalPluginArguments = value; });

    DafnyOptions.RegisterLegacyBinding(StdIn, (options, value) => {
      options.UseStdin = value;
    });

    DafnyOptions.RegisterLegacyBinding(Prelude, (options, value) => {
      options.DafnyPrelude = value?.FullName;
      options.ExpandFilename(options.DafnyPrelude, x => options.DafnyPrelude = x, options.LogPrefix,
        options.FileTimestamp);
    });

    DafnyOptions.RegisterLegacyBinding(BuildFile, (options, value) => { options.DafnyPrintCompiledFile = value?.FullName; });

    DafnyOptions.RegisterLegacyBinding(Libraries,
      (options, value) => { options.LibraryFiles = SplitOptionValueIntoFiles(value.Select(fi => fi.FullName)).ToHashSet(); });
    DafnyOptions.RegisterLegacyBinding(Output, (options, value) => { options.DafnyPrintCompiledFile = value?.FullName; });

    DafnyOptions.RegisterLegacyBinding(Verbose, (o, v) => o.Verbose = v);
    DafnyOptions.RegisterLegacyBinding(DisableNonLinearArithmetic, (o, v) => o.DisableNLarith = v);
    DafnyOptions.RegisterLegacyBinding(AllowDeprecation, (o, v) => o.DeprecationNoise = v ? 0 : 1);

    DafnyOptions.RegisterLegacyBinding(SpillTranslation, (o, f) => o.SpillTargetCode = f ? 1U : 0U);

    DafnyOptions.RegisterLegacyBinding(EnforceDeterminism, (options, value) => {
      options.ForbidNondeterminism = value;
      if (!options.Get(RelaxDefiniteAssignment)) {
        options.DefiniteAssignmentLevel = 4;
      }
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

    DafnyOptions.RegisterLegacyBinding(ExtractCounterexample, (options, value) => {
      options.ExtractCounterexample = value;
      options.EnhancedErrorMessages = 1;
    });

    DafnyOptions.RegisterLegacyBinding(ShowProofObligationExpressions, (options, value) => {
      options.ShowProofObligationExpressions = value;
    });

    DafnyOptions.RegisterLegacyBinding(RawPointers, (options, value) => {
      if (value && options.Get(CommonOptionBag.Target) != "rs") {
        Console.Error.WriteLine("Error:  --raw-pointers can only be used with --target:rs or -t:rs");
        System.Environment.Exit(1);
      }
    });

    OptionRegistry.RegisterGlobalOption(UnicodeCharacters, OptionCompatibility.CheckOptionMatches);
    OptionRegistry.RegisterGlobalOption(EnforceDeterminism, OptionCompatibility.CheckOptionLocalImpliesLibrary);
    OptionRegistry.RegisterGlobalOption(RelaxDefiniteAssignment, OptionCompatibility.OptionLibraryImpliesLocalError);
    OptionRegistry.RegisterGlobalOption(AllowAxioms, OptionCompatibility.OptionLibraryImpliesLocalError);
    OptionRegistry.RegisterGlobalOption(AllowWarnings, OptionCompatibility.OptionLibraryImpliesLocalWarning);
    OptionRegistry.RegisterGlobalOption(AllowDeprecation, OptionCompatibility.OptionLibraryImpliesLocalWarning);
    OptionRegistry.RegisterGlobalOption(WarnShadowing, OptionCompatibility.OptionLibraryImpliesLocalWarning);
    OptionRegistry.RegisterGlobalOption(UseStandardLibraries, OptionCompatibility.OptionLibraryImpliesLocalError);
    OptionRegistry.RegisterGlobalOption(Referrers, OptionCompatibility.CheckOptionMatches);
    OptionRegistry.RegisterOption(TranslateStandardLibrary, OptionScope.Cli);
    OptionRegistry.RegisterOption(WarnAsErrors, OptionScope.Cli);
    OptionRegistry.RegisterOption(ProgressOption, OptionScope.Cli);
    OptionRegistry.RegisterOption(LogLocation, OptionScope.Cli);
    OptionRegistry.RegisterOption(LogLevelOption, OptionScope.Cli);
    OptionRegistry.RegisterOption(ManualTriggerOption, OptionScope.Module);
    OptionRegistry.RegisterOption(ShowHints, OptionScope.Cli);
    OptionRegistry.RegisterOption(Libraries, OptionScope.Module);
    OptionRegistry.RegisterOption(Output, OptionScope.Cli);
    OptionRegistry.RegisterOption(PluginOption, OptionScope.Cli);
    OptionRegistry.RegisterOption(Prelude, OptionScope.Cli);
    OptionRegistry.RegisterOption(Target, OptionScope.Cli);
    OptionRegistry.RegisterOption(Verbose, OptionScope.Cli);
    OptionRegistry.RegisterOption(JsonOutput, OptionScope.Cli);
    OptionRegistry.RegisterOption(JsonDiagnostics, OptionScope.Cli);
    OptionRegistry.RegisterOption(QuantifierSyntax, OptionScope.Module);
    OptionRegistry.RegisterOption(SpillTranslation, OptionScope.Cli);
    OptionRegistry.RegisterOption(StdIn, OptionScope.Cli);
    OptionRegistry.RegisterOption(TestAssumptions, OptionScope.Cli);
    OptionRegistry.RegisterOption(ManualLemmaInduction, OptionScope.Module);
    OptionRegistry.RegisterOption(TypeInferenceDebug, OptionScope.Cli);
    OptionRegistry.RegisterOption(GeneralTraits, OptionScope.Cli);
    OptionRegistry.RegisterOption(GeneralNewtypes, OptionScope.Cli);
    OptionRegistry.RegisterOption(TypeSystemRefresh, OptionScope.Cli);
    OptionRegistry.RegisterOption(VerificationLogFormat, OptionScope.Cli);
    OptionRegistry.RegisterOption(VerifyIncludedFiles, OptionScope.Cli);
    OptionRegistry.RegisterOption(DisableNonLinearArithmetic, OptionScope.Module);
    OptionRegistry.RegisterOption(NewTypeInferenceDebug, OptionScope.Cli);
    OptionRegistry.RegisterOption(UseBaseFileName, OptionScope.Cli);
    OptionRegistry.RegisterOption(EmitUncompilableCode, OptionScope.Cli);
    OptionRegistry.RegisterOption(RawPointers, OptionScope.Cli);
    OptionRegistry.RegisterOption(WarnMissingConstructorParenthesis, OptionScope.Module);
    OptionRegistry.RegisterOption(IncludeRuntimeOption, OptionScope.Cli);
    OptionRegistry.RegisterOption(InternalIncludeRuntimeOptionForExecution, OptionScope.Cli);
    OptionRegistry.RegisterOption(WarnContradictoryAssumptions, OptionScope.Module);
    OptionRegistry.RegisterOption(WarnRedundantAssumptions, OptionScope.Module);
    OptionRegistry.RegisterOption(SuggestProofRefactoring, OptionScope.Module);
    OptionRegistry.RegisterOption(AnalyzeProofs, OptionScope.Module);
    OptionRegistry.RegisterOption(VerificationCoverageReport, OptionScope.Cli);
    OptionRegistry.RegisterOption(NoTimeStampForCoverageReport, OptionScope.Cli);
    OptionRegistry.RegisterOption(DefaultFunctionOpacity, OptionScope.Module);
    OptionRegistry.RegisterOption(OptimizeErasableDatatypeWrapper, OptionScope.Cli); // TODO needs translation record registration
    OptionRegistry.RegisterOption(AddCompileSuffix, OptionScope.Cli);  // TODO needs translation record registration
    OptionRegistry.RegisterOption(SystemModule, OptionScope.Cli);
    OptionRegistry.RegisterOption(ExecutionCoverageReport, OptionScope.Cli);
    OptionRegistry.RegisterOption(ExtractCounterexample, OptionScope.Cli);
    OptionRegistry.RegisterOption(ShowProofObligationExpressions, OptionScope.Cli);
    OptionRegistry.RegisterOption(InputType, OptionScope.Cli);
    OptionRegistry.RegisterOption(PrintDiagnosticsRanges, OptionScope.Cli);
    OptionRegistry.RegisterOption(WaitForDebugger, OptionScope.Cli);
    OptionRegistry.RegisterOption(IgnoreIndentation, OptionScope.Cli);
    OptionRegistry.RegisterOption(CheckSourceLocationConsistency, OptionScope.Cli);
  }
}

