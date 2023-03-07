// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

using System;
using System.Collections.Generic;
using System.Collections.ObjectModel;
using System.CommandLine;
using System.CommandLine.Binding;
using System.CommandLine.Parsing;
using System.Diagnostics;
using System.Linq;
using System.Diagnostics.Contracts;
using System.IO;
using System.Reflection;
using System.Text.RegularExpressions;
using JetBrains.Annotations;
using Microsoft.Dafny;
using Microsoft.Dafny.Compilers;
using Microsoft.Dafny.Plugins;
using Bpl = Microsoft.Boogie;

namespace Microsoft.Dafny {
  public enum FunctionSyntaxOptions {
    Version3,
    Migration3To4,
    ExperimentalTreatUnspecifiedAsGhost,
    ExperimentalTreatUnspecifiedAsCompiled,
    ExperimentalPredicateAlwaysGhost,
    Version4,
  }

  public enum QuantifierSyntaxOptions {
    Version3,
    Version4,
  }

  public record Options(IDictionary<Option, object> OptionArguments);

  public class DafnyOptions : Bpl.CommandLineOptions {

    static DafnyOptions() {
      RegisterLegacyUi(CommonOptionBag.Target, ParseString, "Compilation options", "compileTarget", @"
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

      RegisterLegacyUi(CommonOptionBag.OptimizeErasableDatatypeWrapper, ParseBoolean, "Compilation options", "optimizeErasableDatatypeWrapper", @"
0 - Include all non-ghost datatype constructors in the compiled code
1 (default) - In the compiled target code, transform any non-extern
    datatype with a single non-ghost constructor that has a single
    non-ghost parameter into just that parameter. For example, the type
        datatype Record = Record(x: int)
    is transformed into just 'int' in the target code.".TrimStart(), defaultValue: true);

      RegisterLegacyUi(CommonOptionBag.Output, ParseFileInfo, "Compilation options", "out");
      RegisterLegacyUi(CommonOptionBag.UnicodeCharacters, ParseBoolean, "Language feature selection", "unicodeChar", @"
0 - The char type represents any UTF-16 code unit.
1 (default) - The char type represents any Unicode scalar value.".TrimStart(), defaultValue: true);
      RegisterLegacyUi(CommonOptionBag.Plugin, ParseStringElement, "Plugins", defaultValue: new List<string>());
      RegisterLegacyUi(CommonOptionBag.Prelude, ParseFileInfo, "Input configuration", "dprelude");

      RegisterLegacyUi(CommonOptionBag.Libraries, ParseStringElement, "Compilation options", defaultValue: new List<string>());
      RegisterLegacyUi(DeveloperOptionBag.ResolvedPrint, ParseString, "Overall reporting and printing", "rprint");
      RegisterLegacyUi(DeveloperOptionBag.Print, ParseString, "Overall reporting and printing", "dprint");

      RegisterLegacyUi(DafnyConsolePrinter.ShowSnippets, ParseBoolean, "Overall reporting and printing", "showSnippets", @"
0 (default) - Don't show source code snippets for Dafny messages.
1 - Show a source code snippet for each Dafny message.".TrimStart());

      RegisterLegacyUi(Microsoft.Dafny.Printer.PrintMode, ParsePrintMode, "Overall reporting and printing", "printMode", legacyDescription: @"
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

      void ParsePrintMode(Option<PrintModes> option, Bpl.CommandLineParseState ps, DafnyOptions options) {
        if (ps.ConfirmArgumentCount(1)) {
          if (ps.args[ps.i].Equals("Everything")) {
            options.Set(option, PrintModes.Everything);
          } else if (ps.args[ps.i].Equals("NoIncludes")) {
            options.Set(option, PrintModes.NoIncludes);
          } else if (ps.args[ps.i].Equals("NoGhost")) {
            options.Set(option, PrintModes.NoGhost);
          } else if (ps.args[ps.i].Equals("DllEmbed")) {
            options.Set(option, PrintModes.DllEmbed);
          } else {
            ps.Error("Invalid argument \"{0}\" to option {1}", ps.args[ps.i], option.Name);
          }
        }
      }
    }

    public void ApplyBinding(Option option) {
      if (legacyBindings.ContainsKey(option)) {
        legacyBindings[option](this, Get(option));
      }
    }

    public T Get<T>(Option<T> option) {
      return (T)Options.OptionArguments.GetOrCreate(option, () => default(T));
    }

    public object Get(Option option) {
      return Options.OptionArguments[option];
    }

    public void SetUntyped(Option option, object value) {
      Options.OptionArguments[option] = value;
    }

    public void Set<T>(Option<T> option, T value) {
      Options.OptionArguments[option] = value;
    }

    public void AddFile(string file) => base.AddFile(file, null);

    private static Dictionary<Option, Action<DafnyOptions, object>> legacyBindings = new();
    public static void RegisterLegacyBinding<T>(Option<T> option, Action<DafnyOptions, T> bind) {
      legacyBindings[option] = (options, o) => bind(options, (T)o);
    }

    public static void ParseFileInfo(Option<FileInfo> option, Bpl.CommandLineParseState ps, DafnyOptions options) {
      if (ps.ConfirmArgumentCount(1)) {
        options.Set(option, new FileInfo(ps.args[ps.i]));
      }
    }

    public static void ParseString(Option<string> option, Bpl.CommandLineParseState ps, DafnyOptions options) {
      if (ps.ConfirmArgumentCount(1)) {
        options.Set(option, ps.args[ps.i]);
      }
    }

    public static void ParseStringElement(Option<IList<string>> option, Bpl.CommandLineParseState ps, DafnyOptions options) {
      var value = (IList<string>)options.Options.OptionArguments.GetOrCreate(option, () => new List<string>());
      if (ps.ConfirmArgumentCount(1)) {
        value.Add(ps.args[ps.i]);
      }
    }

    public static void ParseBoolean(Option<bool> option, Bpl.CommandLineParseState ps, DafnyOptions options) {
      int result = 0;
      if (ps.GetIntArgument(ref result, 2)) {
        options.Set(option, result == 1);
      }
    }

    private static readonly List<LegacyUiForOption> legacyUis = new();

    public static void RegisterLegacyUi<T>(Option<T> option,
      Action<Option<T>, Bpl.CommandLineParseState, DafnyOptions> parse,
      string category, string legacyName = null, string legacyDescription = null, T defaultValue = default(T), string argumentName = null) {
      legacyUis.Add(new LegacyUiForOption(
        option,
        (state, options) => parse(option, state, options),
        category,
        legacyName ?? option.Name,
        legacyDescription ?? option.Description,
        argumentName ?? option.ArgumentHelpName ?? "value",
        defaultValue));
    }

    public static DafnyOptions Create(params string[] arguments) {
      var result = new DafnyOptions();
      result.Parse(arguments);
      return result;
    }

    public override bool Parse(string[] arguments) {
      int i;
      for (i = 0; i < arguments.Length; i++) {
        if (arguments[i] == "--args") {
          break;
        }
      }

      if (i >= arguments.Length) {
        return base.Parse(arguments);
      }
      MainArgs = arguments.Skip(i + 1).ToList();
      return base.Parse(arguments.Take(i).ToArray());
    }

    public DafnyOptions()
      : base("dafny", "Dafny program verifier", new DafnyConsolePrinter()) {
      ErrorTrace = 0;
      Prune = true;
      NormalizeNames = true;
      EmitDebugInformation = false;
      Backend = new CsharpBackend();
    }

    public override string VersionNumber {
      get {
        return System.Diagnostics.FileVersionInfo
          .GetVersionInfo(Assembly.GetExecutingAssembly().Location).FileVersion;
      }
    }

    public Options Options { get; set; } = new(new Dictionary<Option, object>());

    public override string Version {
      get { return ToolName + VersionSuffix; }
    }

    public override string VersionSuffix {
      get { return " " + VersionNumber; }
    }

    public bool RunLanguageServer { get; set; }

    private static DafnyOptions clo;

    public static DafnyOptions O {
      get { return clo; }
    }

    public static void Install(DafnyOptions options) {
      Contract.Requires(options != null);
      clo = options;
    }

    public enum DiagnosticsFormats {
      PlainText,
      JSON,
    }

    public bool UsingNewCli = false;
    public bool UnicodeOutput = false;
    public DiagnosticsFormats DiagnosticsFormat = DiagnosticsFormats.PlainText;
    public bool DisallowSoundnessCheating = false;
    public int Induction = 4;
    public int InductionHeuristic = 6;
    public bool TypeInferenceDebug = false;
    public string DafnyPrelude = null;
    public string DafnyPrintFile = null;
    public List<string> FoldersToFormat { get; } = new();

    public enum ContractTestingMode {
      None,
      Externs,
      TestedExterns,
    }

    public PrintModes PrintMode = PrintModes.Everything; // Default to printing everything
    public bool DafnyVerify = true;
    public string DafnyPrintResolvedFile = null;
    public List<string> DafnyPrintExportedViews = new List<string>();
    public bool Compile = true;
    public List<string> MainArgs = new List<string>();
    public bool Format = false;
    public bool FormatCheck = false;

    public string CompilerName;
    public IExecutableBackend Backend;
    public bool CompileVerbose = true;
    public bool EnforcePrintEffects = false;
    public string DafnyPrintCompiledFile = null;
    public string CoverageLegendFile = null;
    public string MainMethod = null;
    public bool RunAllTests = false;
    public bool ForceCompile = false;
    public bool RunAfterCompile = false;
    public uint SpillTargetCode = 0; // [0..4]
    public bool DisallowIncludes = false;
    public bool DisallowExterns = false;
    public bool DisableNLarith = false;
    public int ArithMode = 1; // [0..10]
    public string AutoReqPrintFile = null;
    public bool ignoreAutoReq = false;
    public bool AllowGlobals = false;
    public bool Optimize = false;
    public bool AutoTriggers = true;
    public bool RewriteFocalPredicates = true;
    public bool PrintTooltips = false;
    public bool PrintStats = false;
    public bool DisallowConstructorCaseWithoutParentheses = false;
    public bool PrintFunctionCallGraph = false;
    public bool WarnShadowing = false;
    public FunctionSyntaxOptions FunctionSyntax = FunctionSyntaxOptions.Version4;
    public QuantifierSyntaxOptions QuantifierSyntax = QuantifierSyntaxOptions.Version4;
    public int DefiniteAssignmentLevel = 1; // [0..5] 2 and 3 have the same effect, 4 turns off an array initialisation check and field initialization check, unless --enforce-determinism is used.
    public HashSet<string> LibraryFiles { get; set; } = new();
    public ContractTestingMode TestContracts = ContractTestingMode.None;

    public bool ForbidNondeterminism { get; set; }

    public int DeprecationNoise = 1;
    public bool VerifyAllModules = false;
    public bool SeparateModuleOutput = false;

    public enum IncludesModes {
      None,
      Immediate,
      Transitive
    }

    public IncludesModes PrintIncludesMode = IncludesModes.None;
    public int OptimizeResolution = 2;
    public bool UseRuntimeLib = false;
    public bool DisableScopes = false;
    public int Allocated = 4;
    public bool UseStdin = false;
    public bool WarningsAsErrors = false;
    [CanBeNull] private TestGenerationOptions testGenOptions = null;
    public bool ExtractCounterexample = false;
    public List<string> VerificationLoggerConfigs = new();

    public bool AuditProgram = false;

    public static string DefaultZ3Version = "4.12.1";

    public static readonly ReadOnlyCollection<Plugin> DefaultPlugins = new(new[] { SinglePassCompiler.Plugin });
    private IList<Plugin> cliPluginCache;
    public IList<Plugin> Plugins => cliPluginCache ??= ComputePlugins();
    public List<Plugin> AdditionalPlugins = new();
    public IList<string> AdditionalPluginArguments = new List<string>();

    IList<Plugin> ComputePlugins() {
      var result = new List<Plugin>(DefaultPlugins.Concat(AdditionalPlugins));
      foreach (var pluginAndArgument in AdditionalPluginArguments) {
        try {
          var pluginArray = pluginAndArgument.Split(',');
          var pluginPath = pluginArray[0];
          var arguments = Array.Empty<string>();
          if (pluginArray.Length >= 2) {
            // There are no commas in paths, but there can be in arguments
            var argumentsString = string.Join(',', pluginArray.Skip(1));
            // Parse arguments, accepting and remove double quotes that isolate long arguments
            arguments = ParsePluginArguments(argumentsString);
          }

          result.Add(AssemblyPlugin.Load(pluginPath, arguments));
        } catch (Exception e) {
          result.Add(new ErrorPlugin(pluginAndArgument, e));
        }
      }

      return result;
    }

    private static string[] ParsePluginArguments(string argumentsString) {
      var splitter = new Regex(@"""(?<escapedArgument>(?:[^""\\]|\\\\|\\"")*)""|(?<rawArgument>[^ ]+)");
      var escapedChars = new Regex(@"(?<escapedDoubleQuote>\\"")|\\\\");
      return splitter.Matches(argumentsString).Select(
        matchResult =>
          matchResult.Groups["escapedArgument"].Success
            ? escapedChars.Replace(matchResult.Groups["escapedArgument"].Value,
              matchResult2 => matchResult2.Groups["escapedDoubleQuote"].Success ? "\"" : "\\")
            : matchResult.Groups["rawArgument"].Value
      ).ToArray();
    }

    /// <summary>
    /// Automatic shallow-copy constructor
    /// </summary>
    public DafnyOptions(DafnyOptions src) : this() {
      src.CopyTo(this);
    }

    public void CopyTo(DafnyOptions dst) {
      var type = typeof(DafnyOptions);
      while (type != null) {
        var fields = type.GetFields(BindingFlags.NonPublic | BindingFlags.Public | BindingFlags.Instance);
        foreach (var fi in fields) {
          fi.SetValue(dst, fi.GetValue(this));
        }
        type = type.BaseType;
      }
    }

    public virtual TestGenerationOptions TestGenOptions =>
      testGenOptions ??= new TestGenerationOptions();

    protected override bool ParseOption(string name, Bpl.CommandLineParseState ps) {
      if (ParseDafnySpecificOption(name, ps)) {
        return true;
      }

      foreach (var option in legacyUis.Where(o => o.Name == name)) {
        option.Parse(ps, this);
        return true;
      }

      return ParseBoogieOption(name, ps);
    }

    protected bool ParseBoogieOption(string name, Bpl.CommandLineParseState ps) {
      return base.ParseOption(name, ps);
    }

    public override string Help => "Use 'dafny --help' to see help for a newer Dafny CLI format.\n" +
      LegacyUiForOption.GenerateHelp(base.Help, legacyUis, true);

    protected bool ParseDafnySpecificOption(string name, Bpl.CommandLineParseState ps) {
      var args = ps.args; // convenient synonym
      switch (name) {

        case "view":
          if (ps.ConfirmArgumentCount(1)) {
            DafnyPrintExportedViews = args[ps.i].Split(',').ToList();
          }

          return true;

        case "compile": {
            int compile = 0;
            if (ps.GetIntArgument(ref compile, 5)) {
              // convert option to two booleans
              Compile = compile != 0;
              ForceCompile = compile == 2 || compile == 4;
              RunAfterCompile = compile == 3 || compile == 4;
            }

            return true;
          }

        case "compileVerbose": {
            int verbosity = 0;
            if (ps.GetIntArgument(ref verbosity, 2)) {
              CompileVerbose = verbosity == 1;
            }

            return true;
          }

        case "trackPrintEffects": {
            int printEffects = 0;
            if (ps.GetIntArgument(ref printEffects, 2)) {
              EnforcePrintEffects = printEffects == 1;
            }

            return true;
          }

        case "Main":
        case "main": {
            if (ps.ConfirmArgumentCount(1)) {
              MainMethod = args[ps.i];
            }

            return true;
          }

        case "check": {
            if (!ps.hasColonArgument || ps.ConfirmArgumentCount(1)) {
              FormatCheck = !ps.hasColonArgument || args[ps.i] == "1";
            }

            return true;
          }

        case "runAllTests": {
            int runAllTests = 0;
            if (ps.GetIntArgument(ref runAllTests, 2)) {
              RunAllTests = runAllTests != 0; // convert to boolean
            }

            return true;
          }

        case "dafnyVerify": {
            int verify = 0;
            if (ps.GetIntArgument(ref verify, 2)) {
              DafnyVerify = verify != 0; // convert to boolean
            }

            return true;
          }

        case "diagnosticsFormat": {
            if (ps.ConfirmArgumentCount(1)) {
              switch (args[ps.i]) {
                case "json":
                  Printer = new DafnyJsonConsolePrinter { Options = this };
                  DiagnosticsFormat = DiagnosticsFormats.JSON;
                  break;
                case "text":
                  Printer = new DafnyConsolePrinter { Options = this };
                  DiagnosticsFormat = DiagnosticsFormats.PlainText;
                  break;
                case var df:
                  ps.Error($"Unsupported diagnostic format: '{df}'; expecting one of 'json', 'text'.");
                  break;
              }
            }

            return true;
          }

        case "spillTargetCode": {
            uint spill = 0;
            if (ps.GetUnsignedNumericArgument(ref spill, x => true)) {
              SpillTargetCode = spill;
            }

            return true;
          }

        case "coverage": {
            if (ps.ConfirmArgumentCount(1)) {
              CoverageLegendFile = args[ps.i];
            }

            return true;
          }

        case "noCheating": {
            int cheat = 0; // 0 is default, allows cheating
            if (ps.GetIntArgument(ref cheat, 2)) {
              DisallowSoundnessCheating = cheat == 1;
            }

            return true;
          }

        case "titrace":
          TypeInferenceDebug = true;
          return true;

        case "induction":
          ps.GetIntArgument(ref Induction, 5);
          return true;

        case "inductionHeuristic":
          ps.GetIntArgument(ref InductionHeuristic, 7);
          return true;

        case "noIncludes":
          DisallowIncludes = true;
          return true;

        case "noExterns":
          DisallowExterns = true;
          return true;

        case "noNLarith":
          DisableNLarith = true;
          return true;

        case "arith": {
            int a = 0;
            if (ps.GetIntArgument(ref a, 11)) {
              ArithMode = a;
            }

            return true;
          }

        case "mimicVerificationOf":
          if (ps.ConfirmArgumentCount(1)) {
            if (args[ps.i] == "3.3") {
              Prune = false;
              NormalizeNames = false;
              EmitDebugInformation = true;
              NormalizeDeclarationOrder = false;
            } else {
              ps.Error("Mimic verification is not supported for Dafny version {0}", ps.args[ps.i]);
            }
          }

          return true;

        case "autoReqPrint":
          if (ps.ConfirmArgumentCount(1)) {
            AutoReqPrintFile = args[ps.i];
          }

          return true;

        case "noAutoReq":
          ignoreAutoReq = true;
          return true;

        case "allowGlobals":
          AllowGlobals = true;
          return true;

        case "stats":
          PrintStats = true;
          return true;

        case "funcCallGraph":
          PrintFunctionCallGraph = true;
          return true;

        case "warnShadowing":
          WarnShadowing = true;
          return true;

        case "verifyAllModules":
          VerifyAllModules = true;
          return true;

        case "separateModuleOutput":
          SeparateModuleOutput = true;
          return true;

        case "deprecation": {
            int d = 1;
            if (ps.GetIntArgument(ref d, 3)) {
              DeprecationNoise = d;
            }

            return true;
          }

        case "functionSyntax":
          if (ps.ConfirmArgumentCount(1)) {
            if (args[ps.i] == "3") {
              FunctionSyntax = FunctionSyntaxOptions.Version3;
            } else if (args[ps.i] == "4") {
              FunctionSyntax = FunctionSyntaxOptions.Version4;
            } else if (args[ps.i] == "migration3to4") {
              FunctionSyntax = FunctionSyntaxOptions.Migration3To4;
            } else if (args[ps.i] == "experimentalDefaultGhost") {
              FunctionSyntax = FunctionSyntaxOptions.ExperimentalTreatUnspecifiedAsGhost;
            } else if (args[ps.i] == "experimentalDefaultCompiled") {
              FunctionSyntax = FunctionSyntaxOptions.ExperimentalTreatUnspecifiedAsCompiled;
            } else if (args[ps.i] == "experimentalPredicateAlwaysGhost") {
              FunctionSyntax = FunctionSyntaxOptions.ExperimentalPredicateAlwaysGhost;
            } else {
              InvalidArgumentError(name, ps);
            }
          }

          return true;

        case "quantifierSyntax":
          if (ps.ConfirmArgumentCount(1)) {
            if (args[ps.i] == "3") {
              QuantifierSyntax = QuantifierSyntaxOptions.Version3;
            } else if (args[ps.i] == "4") {
              QuantifierSyntax = QuantifierSyntaxOptions.Version4;
            } else {
              InvalidArgumentError(name, ps);
            }
          }

          return true;

        case "printTooltips":
          PrintTooltips = true;
          return true;

        case "warnMissingConstructorParentheses":
          DisallowConstructorCaseWithoutParentheses = true;
          return true;

        case "autoTriggers": {
            int autoTriggers = 0;
            if (ps.GetIntArgument(ref autoTriggers, 2)) {
              AutoTriggers = autoTriggers == 1;
            }

            return true;
          }

        case "rewriteFocalPredicates": {
            int rewriteFocalPredicates = 0;
            if (ps.GetIntArgument(ref rewriteFocalPredicates, 2)) {
              RewriteFocalPredicates = rewriteFocalPredicates == 1;
            }

            return true;
          }

        case "optimize": {
            Optimize = true;
            return true;
          }

        case "allocated": {
            ps.GetIntArgument(ref Allocated, 5);
            if (Allocated != 4) {
              Printer.AdvisoryWriteLine(Console.Out, "The /allocated:<n> option is deprecated");
            }
            return true;
          }

        case "optimizeResolution": {
            int d = 2;
            if (ps.GetIntArgument(ref d, 3)) {
              OptimizeResolution = d;
            }

            return true;
          }

        case "definiteAssignment": {
            int da = 0;
            if (ps.GetIntArgument(ref da, 5)) {
              DefiniteAssignmentLevel = da;
            }

            if (da == 3) {
              ForbidNondeterminism = true;
            }

            return true;
          }

        case "useRuntimeLib": {
            UseRuntimeLib = true;
            return true;
          }

        case "disableScopes": {
            DisableScopes = true;
            return true;
          }

        case "printIncludes":
          if (ps.ConfirmArgumentCount(1)) {
            if (args[ps.i].Equals("None")) {
              PrintIncludesMode = IncludesModes.None;
            } else if (args[ps.i].Equals("Immediate")) {
              PrintIncludesMode = IncludesModes.Immediate;
            } else if (args[ps.i].Equals("Transitive")) {
              PrintIncludesMode = IncludesModes.Transitive;
            } else {
              InvalidArgumentError(name, ps);
            }

            if (PrintIncludesMode == IncludesModes.Immediate || PrintIncludesMode == IncludesModes.Transitive) {
              Compile = false;
              DafnyVerify = false;
            }
          }

          return true;

        case "stdin": {
            UseStdin = true;
            return true;
          }

        case "warningsAsErrors":
          WarningsAsErrors = true;
          return true;

        case "extractCounterexample":
          ExtractCounterexample = true;
          return true;

        case "verificationLogger":
          if (ps.ConfirmArgumentCount(1)) {
            if (args[ps.i].StartsWith("trx") || args[ps.i].StartsWith("csv") || args[ps.i].StartsWith("text")) {
              VerificationLoggerConfigs.Add(args[ps.i]);
            } else {
              InvalidArgumentError(name, ps);
            }
          }
          return true;

        case "testContracts":
          if (ps.ConfirmArgumentCount(1)) {
            if (args[ps.i].Equals("Externs")) {
              TestContracts = ContractTestingMode.Externs;
            } else if (args[ps.i].Equals("TestedExterns")) {
              TestContracts = ContractTestingMode.TestedExterns;
            } else {
              InvalidArgumentError(name, ps);
            }
          }
          return true;
      }

      // Unless this is an option for test generation, defer to superclass
      return TestGenOptions.ParseOption(name, ps) || base.ParseOption(name, ps);
    }

    private static string[] ParseInnerArguments(string argumentsString) {
      var splitter = new Regex(@"""(?<escapedArgument>(?:[^""\\]|\\\\|\\"")*)""|(?<rawArgument>[^ ]+)");
      var escapedChars = new Regex(@"(?<escapedDoubleQuote>\\"")|\\\\");
      return splitter.Matches(argumentsString).Select(
        matchResult =>
          matchResult.Groups["escapedArgument"].Success
          ? escapedChars.Replace(matchResult.Groups["escapedArgument"].Value,
            matchResult2 => matchResult2.Groups["escapedDoubleQuote"].Success ? "\"" : "\\")
          : matchResult.Groups["rawArgument"].Value
      ).ToArray();
    }

    protected void InvalidArgumentError(string name, Bpl.CommandLineParseState ps) {
      ps.Error("Invalid argument \"{0}\" to option {1}", ps.args[ps.i], name);
    }

    public override void ApplyDefaultOptions() {
      foreach (var legacyUiOption in legacyUis) {
        if (!Options.OptionArguments.ContainsKey(legacyUiOption.Option)) {
          Options.OptionArguments[legacyUiOption.Option] = legacyUiOption.DefaultValue;
        }
        if (legacyBindings.ContainsKey(legacyUiOption.Option)) {
          var value = Get(legacyUiOption.Option);
          legacyBindings[legacyUiOption.Option](this, value);
        }
      }

      ApplyDefaultOptionsWithoutSettingsDefault();
    }

    public void ApplyDefaultOptionsWithoutSettingsDefault() {
      base.ApplyDefaultOptions();

      Backend ??= new CsharpBackend();

      // expand macros in filenames, now that LogPrefix is fully determined

      if (!ProverOptions.Any(x => x.StartsWith("SOLVER=") && !x.EndsWith("=z3"))) {
        var z3Version = SetZ3ExecutablePath();
        SetZ3Options(z3Version);
      }

      // Ask Boogie to perform abstract interpretation
      UseAbstractInterpretation = true;
      Ai.J_Intervals = true;
    }

    public override string AttributeHelp =>
      @"Dafny: The documentation about attributes is best viewed here:
      https://dafny-lang.github.io/dafny/DafnyRef/DafnyRef#sec-attributes
      
     The following attributes are supported by this version.
    {:extern}
    {:extern <s1:string>}
    {:extern <s1:string>, <s2:string>}
      NOTE: :extern is target-language dependent.
      The extern modifier is used
        * to alter the CompileName of entities such as modules, classes, methods, etc.,
        * to alter the ReferenceName of the entities,
        * to decide how to define external opaque types,
        * to decide whether to emit target code or not, and
        * to decide whether a declaration is allowed not to have a body.
      The CompileName is the name for the entity when translating to one of the target languages.
      The ReferenceName is the name used to refer to the entity in the target language.
      A common use case of :extern is to avoid name clashes with existing library functions.

      :extern takes 0, 1, or 2 (possibly empty) string arguments:
        - 0: Dafny will use the Dafny name as the CompileName and not affect the ReferenceName
        - 1: Dafny will use s1 as the CompileName, and replaces the last portion of the ReferenceName by s1.
             When used on an opaque type, s1 is used as a hint as to how to declare that type when compiling.
        - 2: Dafny will use s2 as the CompileName.
             Dafny will use a combination of s1 and s2 such as for example s1.s2 as the ReferenceName
             It may also be the case that one of the arguments is simply ignored.
      Dafny does not perform sanity checks on the arguments---it is the user's responsibility not to generate
      malformed target code.

    {:handle}
      TODO

    {:dllimport}
      TODO

    {:compile}
      The {:compile} attribute takes a boolean argument. It may be applied to any top-level declaration.
      If that argument is false, then that declaration will not be compiled at all.
      
      The difference with {:extern} is that {:extern} will still emit declaration code if necessary,
      whereas {:compile false} will just ignore the declaration for compilation purposes.

    {:main}
      When executing a program, Dafny will first look for a method annotated with {:main}, and otherwise
      will look for `method Main()`, and then execute the first of these two methods found.

    {:axiom}
      Ordinarily, the compiler gives an error for every function or
      method without a body. If the function or method is ghost, then
      marking it with {:axiom} suppresses the error. The {:axiom}
      attribute says you're taking responsibility for the existence
      of a body for the function or method.

    {:abstemious}
      TODO

    {:print}
      This attributes declares that a method may have print effects,
      that is, it may use 'print' statements and may call other methods
      that have print effects. The attribute can be applied to compiled
      methods, constructors, and iterators, and it gives an error if
      applied to functions or ghost methods. An overriding method is
      allowed to use a {:print} attribute only if the overridden method
      does.
      Print effects are enforced only with /trackPrintEffects:1.

    {:nativeType}
      Can be applied to newtype declarations for integer types and
      indicates an expectation of what native type (or not) the
      newtype should compile to.

      If a newtype declaration has no explicit :nativeType attribute,
      then the compiler still attempts to find a suitable native numeric
      type, which is then reflected in an informational message or
      hovertext.

      {:nativeType} and {:nativeType true} say that the type is expected
      to compile to some native numeric type, but leaves it to the
      compiler to choose which one. If no suitable native target type is
      found, an error is generated.

      {:nativeType false} says to avoid using a native numeric type.
      Instead, the type will be compiled as an unbounded integer.

      {:nativeType X} where X is one of the following strings:
        ""byte""      8 bits, unsigned
        ""sbyte""     8 bits, signed
        ""ushort""    16 bits, unsigned
        ""short""     16 bits, signed
        ""uint""      32 bits, unsigned
        ""int""       32 bits, signed
        ""number""    53 bits, signed
        ""ulong""     64 bits, unsigned
        ""long""      64 bits, signed
      says to use the indicated target type. If the target compiler
      does not support X, then an error is generated. Also, if, after
      scrutinizing the constraint predicate, the compiler cannot confirm
      that the type's values will fit in X, an error is generated.

      {:nativeType XX} where XX is a list of strings from the list above,
      says to use the first X in XX that the compiler supports. If
      the compiler doesn't support any native type in XX, then an error
      is generated. Also, unless the compiler can confirm that all of
      the listed native types can fit the type's values, an error is
      generated.

    {:tailrecursion}
      Can be applied to methods and functions to direct compilation of
      recursive calls as tail calls.

      A method or function is _tail recursive_ if all of the following
      points apply:
      * It is not mutually recursive with another method or function.
      * Ignoring any parts of the method/function body that are ghost,
        every recursive call is a tail call (that is, the body has no
        more work to do after a recursive call). Note that any ghost
        code that follows a recursive method call is ignored.
      * In the case of a function, the function is not used as a
        first-class value inside the function body.
      For a function F, this definition is extended to additionally allow
      tail calls to appear in simple expressions like ""E + F(...)"" or
      ""F(...) + E"" for certain operators ""+"" where E does not mention
      F, provided that all such expressions are compatible. These
      are called _simple accumulator_ tail calls.

      By default, Dafny compiles tail recursive methods and functions
      using tail calls, automatically handling simple accumulator tail
      calls.

      {:tailrecursion false} is used to turn off tail calls.

      {:tailrecursion} or {:tailrecursion true} is used to confirm
      that the method/function is compiled and tail recursive. If it
      is not, an error is given.

    {:termination}
      Dafny currently lacks the features needed to specify usable termination
      metrics for trait methods that are dynamically dispatched to method
      implementations given in other modules. This issue and a sketch of a
      solution are described in https://github.com/dafny-lang/dafny/issues/1588.
      Until such features are added to the language, a type `C` that extends a
      trait `T` must be declared in the same module as `T`.
      There is, however, an available loophole: if a programmer is willing to
      take the responsibility that all calls to methods in a trait `T`
      that dynamically dispatch to implementations in other modules terminate,
      then the trait `T` can be marked with `{:termination false}`. This will
      allow `T` to be extended by types declared in modules outside `T`'s module.

      Caution: This loophole is unsound; that is, if a cross-module dynamic
      dispatch fails to terminate, then this and other errors in the program
      may have been overlooked by the verifier.       

      The meaning of `{:termination false}` is defined only on trait declarations.
      It has no meaning if applied to other declarations.

      Applying `{:termination false}` to a trait is similar to the
      effect of declaring each of its methods with `decreases *`, but
      there are several differences.  The biggest difference is that
      `decreases *` is sound, whereas the attribute is not. As such,
      `decreases *` cannot be used with functions, lemmas, or ghost
      methods, and callers of a `decreases *` method must themselves
      be declared with `decreases *`. In contrast, `{:termination false}`
      applies to all functions, lemmas, and methods of the trait, and
      callers do not have to indicate that they are using such a
      trait. Another difference is that `{:termination false}` does
      not change checking for intra-module calls. That is, even if a
      trait is declared with `{:termination false}`, calls to its
      functions, lemmas, and methods from within the module where the
      trait is declared are checked for termination in the usual
      manner.

    {:options ""/opt0:xyz"", ""/opt1"", ...}
      When applied to a module, this attribute configures Dafny as if
      `/opt0:xyz` and `/opt1` had been passed on the command line.
      Outside of the module, options revert to their previous values.
      Supported options: %SUPPORTED_OPTIONS%.

    {:warnShadowing}
      TODO

    {:verify}
      TODO

    {:autocontracts}
      TODO

    {:opaque}
      TODO

    {:autoReq}
      When applied to a function definition, Dafny automatically
      strengthens that function's `requires` clause sufficiently so that
      it may call each of the functions that it calls.

      When applied to a module, this attribute is inherited by every
      function in the module.

      The `/autoReqPrint:<file>` option will print out the inferred,
      stronger requires clauses to the given file. The `/noAutoReq`
      option instructs Dafny to ignore any `{:autoReq}` attributes.

    {:timeLimitMultiplier}
      TODO

    {:no_inline}
      When predicates such as `predicate P(x: int) { x % 2 == 0 }`
      are used in assertions like `assert P(6);`, Dafny
      will by default try to figure out if it can split the call
      into multiple assertions that are easier for the verifier.
      Hence, sometimes, if allowed to do so (e.g. no `{:opaque}`),
      Dafny will inline the predicate, resulting in, for example,
      `assert 6 % 2 == 0`.
      
      Adding the attribute `{:no_inline}` to a function will prevent
      the Dafny verifier from inlining it, but unless the function is
      `{:opaque}` its definition will still be available.
      
      This trick can be helpful, for a huge conjunct predicate `P`,
      assuming that `P(x)` already hold, if we don't want `P`
      to be opaque, and we `assert P(x)` again. Inlining might result
      in performance issues because it will have to infer every single
      conjunct. Adding `{:no_inline}` to the predicate can result
      in such cases in the verifier being faster.

    {:nowarn}
      TODO

    {:autotriggers}
      TODO

    {:trigger}
      TODO".Replace("%SUPPORTED_OPTIONS%",
        string.Join(", ", DafnyAttributeOptions.KnownOptions));

    /// <summary>
    /// Dafny releases come with their own copy of Z3, to save users the trouble of having to install extra dependencies.
    /// For this to work, Dafny first tries any prover path explicitly provided by the user, then looks for for the copy
    /// distributed with Dafny, and finally looks in any directory in the system PATH environment variable.
    /// </summary>
    private Version SetZ3ExecutablePath() {
      string confirmedProverPath = null;

      // Try an explicitly provided prover path, if there is one.
      var pp = "PROVER_PATH=";
      var proverPathOption = ProverOptions.Find(o => o.StartsWith(pp));
      if (proverPathOption != null) {
        var proverPath = proverPathOption.Substring(pp.Length);
        // Boogie will perform the ultimate test to see if "proverPath" is real--it will attempt to run it.
        // However, by at least checking if the file exists, we can produce a better error message in common scenarios.
        // Unfortunately, there doesn't seem to be a portable way of checking whether it's executable.
        if (!File.Exists(proverPath)) {
          return null;
        }

        confirmedProverPath = proverPath;
      }

      var platform = System.Environment.OSVersion.Platform;
      var isUnix = platform == PlatformID.Unix || platform == PlatformID.MacOSX;

      // Next, try looking in a directory relative to Dafny itself.
      if (confirmedProverPath is null) {
        var dafnyBinDir = Path.GetDirectoryName(Assembly.GetExecutingAssembly().Location);
        var z3LocalBinName = isUnix
          ? $"z3-{DefaultZ3Version}"
          : $"z3-{DefaultZ3Version}.exe";
        var z3BinPath = Path.Combine(dafnyBinDir, "z3", "bin", z3LocalBinName);

        if (File.Exists(z3BinPath)) {
          confirmedProverPath = z3BinPath;
        }
      }

      // Finally, try looking in the system PATH variable.
      var z3GlobalBinName = isUnix ? "z3" : "z3.exe";
      if (confirmedProverPath is null) {
        confirmedProverPath = System.Environment
          .GetEnvironmentVariable("PATH")?
          .Split(isUnix ? ':' : ';')
          .Select(s => Path.Combine(s, z3GlobalBinName))
          .FirstOrDefault(File.Exists);
      }

      if (confirmedProverPath is not null) {
        ProverOptions.Add($"{pp}{confirmedProverPath}");
        return GetZ3Version(confirmedProverPath);
      }

      return null;
    }

    private static readonly Regex Z3VersionRegex = new Regex(@"Z3 version (?<major>\d+)\.(?<minor>\d+)\.(?<patch>\d+)");

    [CanBeNull]
    public static Version GetZ3Version(string proverPath) {
      var z3Process = new ProcessStartInfo(proverPath, "-version") {
        CreateNoWindow = true,
        RedirectStandardError = true,
        RedirectStandardOutput = true,
        RedirectStandardInput = true
      };
      var run = Process.Start(z3Process);
      if (run == null) {
        return null;
      }

      var actualOutput = run.StandardOutput.ReadToEnd();
      run.WaitForExit();
      var versionMatch = Z3VersionRegex.Match(actualOutput);
      if (!versionMatch.Success) {
        // Might be another solver.
        return null;
      }

      var major = int.Parse(versionMatch.Groups["major"].Value);
      var minor = int.Parse(versionMatch.Groups["minor"].Value);
      var patch = int.Parse(versionMatch.Groups["patch"].Value);
      return new Version(major, minor, patch);
    }

    // Set a Z3 option, but only if it is not overwriting an existing option.
    private void SetZ3Option(string name, string value) {
      if (!ProverOptions.Any(o => o.StartsWith($"O:{name}="))) {
        ProverOptions.Add($"O:{name}={value}");
      }
    }

    private void SetZ3Options(Version z3Version) {
      // Boogie sets the following Z3 options by default:
      // smt.mbqi = false
      // model.compact = false
      // model.v2 = true
      // pp.bv_literals = false

      // Boogie also used to set the following options, but does not anymore.
      SetZ3Option("auto_config", "false");
      SetZ3Option("type_check", "true");
      SetZ3Option("smt.qi.eager_threshold", "100"); // TODO: try lowering
      SetZ3Option("smt.delay_units", "true");

      // This option helps avoid "time travelling triggers".
      // See: https://github.com/dafny-lang/dafny/discussions/3362
      SetZ3Option("smt.case_split", "3");

      // This option tends to lead to the best all-around arithmetic
      // performance, though some programs can be verified more quickly
      // (or verified at all) using a different solver.
      SetZ3Option("smt.arith.solver", "2");

      if (DisableNLarith || 3 <= ArithMode) {
        SetZ3Option("smt.arith.nl", "false");
      }
    }

    protected override string HelpBody => DafnyHelpBody + BoogieHelpBody;

    protected string BoogieHelpBody => base.HelpBody;

    protected string DafnyHelpBody =>
      $@"
All the .dfy files supplied on the command line along with files recursively
included by 'include' directives are considered a single Dafny program;
however only those files listed on the command line are verified.

Exit code: 0 -- success; 1 -- invalid command-line; 2 -- parse or type errors;
           3 -- compilation errors; 4 -- verification errors

---- Input configuration ---------------------------------------------------

/stdin
    Read standard input and treat it as an input .dfy file.

---- Plugins ---------------------------------------------------------------

---- Overall reporting and printing ----------------------------------------

/stats
    Print interesting statistics about the Dafny files supplied.

/printIncludes:<None|Immediate|Transitive>
    None (default) - Print nothing.
    Immediate - Print files included by files listed on the command line.
    Transitive - Recurses on the files printed by Immediate.

    Immediate and Transitive will exit after printing.

/view:<view1, view2>
    Print the filtered views of a module after it is resolved (/rprint).
    If print before the module is resolved (/dprint), then everything in
    the module is printed. If no view is specified, then everything in
    the module is printed.
/funcCallGraph
    Print out the function call graph. Format is: func,mod=callee*

/pmtrace
    Print pattern-match compiler debug info.

/titrace
    Print type-inference debug info.

/printTooltips
    Dump additional positional information (displayed as mouse-over
    tooltips by the VS Code plugin) to stdout as 'Info' messages.

/diagnosticsFormat:<text|json>
    Choose how to report errors, warnings, and info messages.
    text (default) - Use human readable output
    json - Print each message as a JSON object, one per line.

---- Language feature selection --------------------------------------------

/noIncludes
    Ignore include directives.

/noExterns
    Ignore extern and dllimport attributes.

/functionSyntax:<version>
    The syntax for functions is changing from Dafny version 3 to version
    4. This switch gives early access to the new syntax, and also
    provides a mode to help with migration.

    3 - Compiled functions are written `function method` and
        `predicate method`. Ghost functions are written `function` and
        `predicate`.
    4 (default) - Compiled functions are written `function` and `predicate`. Ghost
        functions are written `ghost function` and `ghost predicate`.
    migration3to4 - Compiled functions are written `function method` and
        `predicate method`. Ghost functions are written `ghost function`
        and `ghost predicate`. To migrate from version 3 to version 4,
        use this flag on your version 3 program. This will give flag all
        occurrences of `function` and `predicate` as parsing errors.
        These are ghost functions, so change those into the new syntax
        `ghost function` and `ghost predicate`. Then, start using
        /functionSyntax:4. This will flag all occurrences of `function
        method` and `predicate method` as parsing errors. So, change
        those to just `function` and `predicate`. Now, your program uses
        version 4 syntax and has the exact same meaning as your previous
        version 3 program.
    experimentalDefaultGhost - Like migration3to4, but allow `function`
        and `predicate` as alternatives to declaring ghost functions and
        predicates, respectively.
    experimentalDefaultCompiled - Like migration3to4, but allow
        `function` and `predicate` as alternatives to declaring compiled
        functions and predicates, respectively.
    experimentalPredicateAlwaysGhost - Compiled functions are written
        `function`. Ghost functions are written `ghost function`.
        Predicates are always ghost and are written `predicate`.

/quantifierSyntax:<version>
    The syntax for quantification domains is changing from Dafny version
    3 to version 4, more specifically where quantifier ranges (|
    <Range>) are allowed. This switch gives early access to the new
    syntax.

    3 - Ranges are only allowed after all quantified variables
        are declared. (e.g. set x, y | 0 <= x < |s| && y in s[x] && 0 <=
        y :: y)
    4 (default) - Ranges are allowed after each quantified variable declaration.
        (e.g. set x | 0 <= x < |s|, y <- s[x] | 0 <= y :: y)

    Note that quantifier variable domains (<- <Domain>) are available in
    both syntax versions.

/disableScopes
    Treat all export sets as 'export reveal *'. i.e. don't hide function
    bodies or type definitions during translation.

/allowGlobals
    Allow the implicit class '_default' to contain fields, instance
    functions, and instance methods. These class members are declared at
    the module scope, outside of explicit classes. This command-line
    option is provided to simplify a transition from the behavior in the
    language prior to version 1.9.3, from which point onward all
    functions and methods declared at the module scope are implicitly
    static and fields declarations are not allowed at the module scope.

---- Warning selection -----------------------------------------------------

/warnShadowing
    Emits a warning if the name of a declared variable caused another
    variable to be shadowed.

/warnMissingConstructorParenthesis
    Emits a warning when a constructor name in a case pattern is not
    followed by parentheses.

/deprecation:<n>
    0 - Don't give any warnings about deprecated features.
    1 (default) - Show warnings about deprecated features.
    2 - Also point out where there's new simpler syntax.

/warningsAsErrors
    Treat warnings as errors.

---- Verification options -------------------------------------------------

/dafnyVerify:<n>
    0 - Stop after resolution and typechecking.
    1 - Continue on to verification and compilation.

/verifyAllModules
    Verify modules that come from an include directive.

/separateModuleOutput
    Output verification results for each module separately, rather than
    aggregating them after they are all finished.

/verificationLogger:<configuration string>
    Logs verification results to the given test result logger. The
    currently supported loggers are `trx`, `csv`, and `text`. These are
    the XML-based format commonly used for test results for .NET
    languages, a custom CSV schema, and a textual format meant for human
    consumption. You can provide configuration using the same string
    format as when using the --logger option for dotnet test, such as:

        /verificationLogger:trx;LogFileName=<...>.

    The exact mapping of verification concepts to these formats is
    experimental and subject to change!

    The `trx` and `csv` loggers automatically choose an output file name
    by default, and print the name of this file to the console. The
    `text` logger prints its output to the console by default, but can
    send output to a file given the `LogFileName` option.

    The `text` logger also includes a more detailed breakdown of what
    assertions appear in each assertion batch. When combined with the
    `/vcsSplitOnEveryAssert` option, it will provide approximate time
    and resource use costs for each assertion, allowing identification
    of especially expensive assertions.

/mimicVerificationOf:<Dafny version>
    Let Dafny attempt to mimic the verification as it was in a previous
    version of Dafny. Useful during migration to a newer version of
    Dafny when a Dafny program has proofs, such as methods or lemmas,
    that are unstable in the sense that their verification may become
    slower or fail altogether after logically irrelevant changes are
    made in the verification input.

    Accepted versions are: 3.3 (note that this turns off features that
    prevent classes of verification instability)

/noCheating:<n>
    0 (default) - Allow assume statements and free invariants.
    1 - Treat all assumptions as asserts, and drop free.

/induction:<n>
    0 - Never do induction, not even when attributes request it.
    1 - Only apply induction when attributes request it.
    2 - Apply induction as requested (by attributes) and also for
        heuristically chosen quantifiers.
    3 - Apply induction as requested, and for heuristically chosen
        quantifiers and lemmas.
    4 (default) - Apply induction as requested, and for lemmas.

/inductionHeuristic:<n>
    0 - Least discriminating induction heuristic (that is, lean toward
        applying induction more often).
    1,2,3,4,5 - Levels in between, ordered as follows as far as how
        discriminating they are: 0 < 1 < 2 < (3,4) < 5 < 6.
    6 (default) - Most discriminating.

/trackPrintEffects:<n>
    0 (default) - Every compiled method, constructor, and iterator,
       whether or not it bears a {{:print}} attribute, may have print
       effects.
    1 - A compiled method, constructor, or iterator is allowed to have
       print effects only if it is marked with {{:print}}.

/allocated:<n>
    This option is deprecated. Going forward, only what is /allocated:4
    will be supported.
    Specify defaults for where Dafny should assert and assume
    allocated(x) for various parameters x, local variables x, bound
    variables x, etc. Lower <n> may require more manual allocated(x)
    annotations and thus may be more difficult to use. Warning: this
    option should be chosen consistently across an entire project; it
    would be unsound to use different defaults for different files or
    modules within a project. And even so, modes /allocated:0 and
    /allocated:1 let functions depend on the allocation state, which is
    not sound in general.

    0 - Nowhere (never assume/assert allocated(x) by default).
    1 - Assume allocated(x) only for non-ghost variables and fields
        (these assumptions are free, since non-ghost variables always
        contain allocated values at run-time). This option may speed up
        verification relative to /allocated:2.
    2 - Assert/assume allocated(x) on all variables, even bound
        variables in quantifiers. This option is the easiest to use for
        heapful code.
    3 - Frugal use of heap parameter (not sound).
    4 - (default) Mode 3 but with alloc antecedents when ranges don't imply
        allocatedness.

/definiteAssignment:<n>
    0 - Ignores definite-assignment rules. This mode is for testing
        only--it is not sound.
    1 (default) - Enforces definite-assignment rules for compiled
        variables and fields whose types do not support
        auto-initialization, and for ghost variables and fields whose
        type is possibly empty.
    2 - Enforces definite-assignment for all non-yield-parameter
        variables and fields, regardless of their types.
    3 - Like 2, but also performs checks in the compiler that no
        nondeterministic statements are used; thus, a program that
        passes at this level 3 is one that the language guarantees that
        values seen during execution will be the same in every run of
        the program.
    4 - Like 1, but enforces definite assignment for all local variables
        and out-parameters, regardless of their types. (Whether or not
        fields and new arrays are subject to definite assignments depends
        on their types.)

/noAutoReq
    Ignore autoReq attributes.

/autoReqPrint:<file>
    Print out requirements that were automatically generated by autoReq.

/noNLarith
    Reduce Z3's knowledge of non-linear arithmetic (*,/,%).

    Results in more manual work, but also produces more predictable
    behavior. (This switch will perhaps be replaced by /arith in the
    future. For now, it takes precedence of /arith.)

/arith:<n>
    (experimental) Adjust how Dafny interprets arithmetic operations.

    0 - Use Boogie/Z3 built-ins for all arithmetic operations.
    1 (default) - Like 0, but introduce symbolic synonyms for *,/,%, and
        allow these operators to be used in triggers.
    2 - Like 1, but introduce symbolic synonyms also for +,-.
    3 - Turn off non-linear arithmetic in the SMT solver. Still, use
        Boogie/Z3 built-in symbols for all arithmetic operations.
    4 - Like 3, but introduce symbolic synonyms for *,/,%, and allow
        these operators to be used in triggers.
    5 - Like 4, but introduce symbolic synonyms also for +,-.
    6 - Like 5, and introduce axioms that distribute + over *.
    7 - like 6, and introduce facts that associate literals arguments of *.
    8 - Like 7, and introduce axiom for the connection between *,/,%.
    9 - Like 8, and introduce axioms for sign of multiplication.
    10 - Like 9, and introduce axioms for commutativity and
        associativity of *.

/autoTriggers:<n>
    0 - Do not generate {{:trigger}} annotations for user-level
        quantifiers.
    1 (default) - Add a {{:trigger}} to each user-level quantifier.
        Existing annotations are preserved.

/rewriteFocalPredicates:<n>
    0 - Don't rewrite predicates in the body of prefix lemmas.
    1 (default) - In the body of prefix lemmas, rewrite any use of a
        focal predicate P to P#[_k-1].

/extractCounterexample
    If verification fails, report a detailed counterexample for the
    first failing assertion. Requires specifying the /mv:<file> option as well
    as /proverOpt:O:model_compress=false (for z3 version < 4.8.7) or
    /proverOpt:O:model.compact=false (for z3 version >= 4.8.7), and
    /proverOpt:O:model.completion=true.

---- Test generation options -----------------------------------------------
{TestGenOptions.Help}
---- Compilation options ---------------------------------------------------

/compile:<n>
    0 - Do not compile Dafny program.
    1 (default) - Upon successful verification of the Dafny program,
        compile it to the designated target language. (/noVerify
        automatically counts as a failed verification.)
    2 - Always attempt to compile Dafny program to the target language,
        regardless of verification outcome.
    3 - If there is a Main method and there are no verification errors
        and /noVerify is not used, compiles program in memory (i.e.,
        does not write an output file) and runs it.
    4 - Like (3), but attempts to compile and run regardless of
        verification outcome.
/Main:<name>
    Specify the (fully-qualified) name of the method to use as the executable entry point.
    Default is the method with the {{:main}} attribute, or else the method named 'Main'.
    A Main method can have at most one (non-ghost) argument of type `seq<string>`
--args <arg1> <arg2> ...
    When running a Dafny file through /compile:3 or /compile:4, '--args' provides
    all arguments after it to the Main function, at index starting at 1.
    Index 0 is used to store the executable's name if it exists.
/runAllTests:<n> (experimental)
    0 (default) - Annotates compiled methods with the {{:test}}
        attribute such that they can be tested using a testing framework
        in the target language (e.g. xUnit for C#).
    1 - Emits a main method in the target language that will execute
        every method in the program with the {{:test}} attribute. Cannot
        be used if the program already contains a main method. Note that
        /compile:3 or 4 must be provided as well to actually execute
        this main method!

/compileVerbose:<n>
    0 - Don't print status of compilation to the console.
    1 (default) - Print information such as files being written by the
        compiler to the console.

/spillTargetCode:<n>
    Explicitly writes the code in the target language to one or more files.
    This is not necessary to run a Dafny program, but may be of interest when
    building multi-language programs or for debugging.

    0 (default) - Don't make any extra effort to write the textual
        target program (but still compile it, if /compile indicates to
        do so).
    1 - Write the textual target program, if it is being compiled.
    2 - Write the textual target program, provided it passes the
        verifier (and /noVerify is NOT used), regardless of /compile
        setting.
    3 - Write the textual target program, regardless of verification
        outcome and /compile setting.
    Note, some compiler targets may (always or in some situations) write
    out the textual target program as part of compilation, in which case
    /spillTargetCode:0 behaves the same way as /spillTargetCode:1.
/coverage:<file>
    The compiler emits branch-coverage calls and outputs into <file> a
    legend that gives a description of each source-location identifier
    used in the branch-coverage calls. (Use - as <file> to print to the
    console.)

/optimize
    Produce optimized C# code by passing the /optimize flag to csc.exe.

/optimizeResolution:<n>
    0 - Resolve and translate all methods.
    1 - Translate methods only in the call graph of current verification
        target.
    2 (default) - As in 1, but only resolve method bodies in
        non-included Dafny sources.
/useRuntimeLib
    Refer to a pre-built DafnyRuntime.dll in the compiled assembly
    rather than including DafnyRuntime.cs verbatim.

/testContracts:<Externs|TestedExterns>
    Enable run-time testing of the compilable portions of certain function
    or method contracts, at their call sites. The current implementation
    focuses on {{:extern}} code but may support other code in the future.

    Externs - Check contracts on every call to a function or method marked
        with the {{:extern}} attribute, regardless of where it occurs.
    TestedExterns - Check contracts on every call to a function or method
        marked with the {{:extern}} attribute when it occurs in a method
        with the {{:test}} attribute, and warn if no corresponding test
        exists for a given external declaration.

----------------------------------------------------------------------------

Dafny generally accepts Boogie options and passes these on to Boogie.
However, some Boogie options, like /loopUnroll, may not be sound for
Dafny or may not have the same meaning for a Dafny program as it would
for a similar Boogie program.
".Replace("\n", "\n  ");
  }

}

class ErrorReportingCommandLineParseState : Bpl.CommandLineParseState {
  private readonly Errors errors;
  private IToken token;

  public ErrorReportingCommandLineParseState(string[] args, string toolName, Errors errors, IToken token)
    : base(args, toolName) {
    this.errors = errors;
    this.token = token;
  }

  public override void Error(string message, params string[] args) {
    errors.SemErr(token, string.Format(message, args));
    EncounteredErrors = true;
  }
}

/// <summary>
/// Wrapper object that restricts which options may be applied.
/// Used by the parser to parse <c>:options</c> strings.
/// </summary>
class DafnyAttributeOptions : DafnyOptions {
  public static readonly HashSet<string> KnownOptions = new() {
    "functionSyntax",
    "quantifierSyntax"
  };

  private readonly Errors errors;
  public IToken Token { get; set; }

  public DafnyAttributeOptions(DafnyOptions opts, Errors errors) : base(opts) {
    this.errors = errors;
    Token = null;
  }

  protected override Bpl.CommandLineParseState InitializeCommandLineParseState(string[] args) {
    return new ErrorReportingCommandLineParseState(args, ToolName, errors, Token ?? Microsoft.Dafny.Token.NoToken);
  }

  private void Unsupported(string name, Bpl.CommandLineParseState ps) {
    ps.Error($"Option {name} unrecognized or unsupported in ':options' attributes.");
  }

  protected override void UnknownSwitch(Bpl.CommandLineParseState ps) {
    Unsupported(ps.s, ps);
  }

  protected override bool ParseOption(string name, Bpl.CommandLineParseState ps) {
    if (!KnownOptions.Contains(name)) {
      return false;
    }
    return base.ParseOption(name, ps);
  }

  protected override void AddFile(string file, Bpl.CommandLineParseState ps) {
    Unsupported(file, ps);
  }
}
