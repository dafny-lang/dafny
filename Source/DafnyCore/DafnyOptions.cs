// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Collections.ObjectModel;
using System.CommandLine;
using System.CommandLine.Binding;
using System.Diagnostics;
using System.Globalization;
using System.Linq;
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

  public record Options(Dictionary<Option, object> OptionArguments, Dictionary<Argument, object> Arguments);

  public class DafnyOptions : Bpl.CommandLineOptions {

    public string GetPrintPath(string path) => UseBaseNameForFileName ? Path.GetFileName(path) : path;
    public TextWriter ErrorWriter { get; set; }
    public TextReader Input { get; }
    public static readonly DafnyOptions Default = new(TextReader.Null, TextWriter.Null, TextWriter.Null);

    public IList<Uri> CliRootSourceUris = new List<Uri>();

    public DafnyProject DafnyProject { get; set; }

    public static void ParseDefaultFunctionOpacity(Option<CommonOptionBag.DefaultFunctionOpacityOptions> option, Bpl.CommandLineParseState ps, DafnyOptions options) {
      if (ps.ConfirmArgumentCount(1)) {
        if (ps.args[ps.i].Equals("transparent")) {
          options.Set(option, CommonOptionBag.DefaultFunctionOpacityOptions.Transparent);
        } else if (ps.args[ps.i].Equals("autoRevealDependencies")) {
          options.Set(option, CommonOptionBag.DefaultFunctionOpacityOptions.AutoRevealDependencies);
        } else if (ps.args[ps.i].Equals("opaque")) {
          options.Set(option, CommonOptionBag.DefaultFunctionOpacityOptions.Opaque);
        } else {
          InvalidArgumentError(option.Name, ps);
        }
      }
    }

    public void ApplyBinding(Option option) {
      if (legacyBindings.ContainsKey(option)) {
        legacyBindings[option](this, Get(option));
      }
    }

    public T Get<T>(Argument<T> argument) {
      return (T)Options.Arguments.GetOrDefault(argument, () => (object)default(T));
    }


    public T Get<T>(Option<T> option) {
      return (T)Options.OptionArguments.GetOrDefault(option, () => (object)default(T));
    }


    public T GetOrOptionDefault<T>(Option<T> option) {
      return (T)Options.OptionArguments.GetOrDefault(option, () =>
       ((IValueDescriptor<T>)option) is {
         HasDefaultValue: true
       } valueDescriptor
          ? valueDescriptor.GetDefaultValue()
          : (object)default(T)
      );
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

    protected override void AddFile(string file, Bpl.CommandLineParseState ps) {
      CliRootSourceUris.Add(new Uri(Path.GetFullPath(file)));
      base.AddFile(file, ps);
    }

    private static Dictionary<Option, Action<DafnyOptions, object>> legacyBindings = new();
    public static void RegisterLegacyBinding<T>(Option<T> option, Action<DafnyOptions, T> bind) {
      legacyBindings[option] = (options, o) => bind(options, (T)o);
    }

    public static void ParseString(Option<string> option, Bpl.CommandLineParseState ps, DafnyOptions options) {
      if (ps.ConfirmArgumentCount(1)) {
        options.Set(option, ps.args[ps.i]);
      }
    }

    private static DafnyOptions defaultImmutableOptions;
    public static DafnyOptions DefaultImmutableOptions => defaultImmutableOptions ??= CreateUsingOldParser(Console.Out, Console.In);

    public static DafnyOptions CreateUsingOldParser(TextWriter outputWriter, TextReader input = null, params string[] arguments) {
      input ??= TextReader.Null;
      var result = new DafnyOptions(input, outputWriter, outputWriter);
      result.Parse(arguments);
      return result;
    }

    protected override Bpl.CommandLineParseState InitializeCommandLineParseState(string[] args) {
      return new TextWriterParseState(args, ToolName, ErrorWriter);
    }

    /// <summary>
    /// Needed because the Boogie version writes to Console.Error
    /// </summary>
    class TextWriterParseState : Bpl.CommandLineParseState {
      private readonly TextWriter errorWriter;

      public TextWriterParseState(string[] args, string toolName, TextWriter errorWriter) : base(args, toolName) {
        this.errorWriter = errorWriter;
      }

      public override void Error(string message, params string[] args) {
        errorWriter.WriteLine("{0}: Error: {1}", ToolName, string.Format(message, args));
        EncounteredErrors = true;
      }
    }

    /// <summary>
    /// Customized version of Microsoft.Boogie.CommandLineOptions.Parse
    /// Needed because the Boogie version writes to Console.Error
    /// </summary>
    public bool BaseParse(string[] args, bool allowFile) {
      Environment = Environment + "Command Line Options: " + string.Join(" ", args);
      args = cce.NonNull<string[]>((string[])args.Clone());
      Bpl.CommandLineParseState state;
      for (state = InitializeCommandLineParseState(args); state.i < args.Length; state.i = state.nextIndex) {
        cce.LoopInvariant(state.args == args);
        string file = args[state.i];
        state.s = file.Trim();
        bool flag = state.s.StartsWith("-") || state.s.StartsWith("/");
        int length = state.s.IndexOf(':');
        if (0 <= length & flag) {
          state.hasColonArgument = true;
          args[state.i] = state.s.Substring(length + 1);
          state.s = state.s.Substring(0, length);
        } else {
          ++state.i;
          state.hasColonArgument = false;
        }
        state.nextIndex = state.i;
        if (flag) {
          if (!ParseOption(state.s.Substring(1), state)) {
            if (Path.DirectorySeparatorChar == '/' && state.s.StartsWith("/")) {
              AddFile(file, state);
            } else {
              UnknownSwitch(state);
            }
          }
        } else if (allowFile) {
          AddFile(file, state);
        } else {
          state.Error($"Boogie option '{state.s}' must start with - or /");
        }
      }
      if (state.EncounteredErrors) {
        ErrorWriter.WriteLine("Use /help for available options");
        return false;
      }
      ApplyDefaultOptions();
      return true;
    }

    public DafnyOptions(TextReader inputReader, TextWriter outputWriter, TextWriter errorWriter)
      : base(outputWriter, "dafny", "Dafny program verifier", new Bpl.ConsolePrinter()) {
      Input = inputReader;
      ErrorWriter = errorWriter;
      ErrorTrace = 0;
      Prune = true;
      TypeEncodingMethod = Bpl.CoreOptions.TypeEncoding.Arguments;
      NormalizeNames = true;
      EmitDebugInformation = false;
      Backend = new CsharpBackend(this);
      Printer = new NullPrinter();
    }

    public override string VersionNumber {
      get {
        return FileVersionInfo
          .GetVersionInfo(Assembly.GetExecutingAssembly().Location).FileVersion;
      }
    }

    public Options Options { get; set; } = new(new Dictionary<Option, object>(), new Dictionary<Argument, object>());

    public override string Version {
      get { return ToolName + VersionSuffix; }
    }

    public override string VersionSuffix {
      get { return " " + VersionNumber; }
    }

    public bool RunLanguageServer { get; set; }

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
    public string DafnyPrelude = null;
    public string DafnyPrintFile = null;
    public bool AllowSourceFolders = false;
    public List<string> SourceFolders { get; } = []; // list of folders, for those commands that permit processing all source files in folders

    public enum ContractTestingMode {
      None,
      Externs,
      TestedExterns,
    }

    public PrintModes PrintMode = PrintModes.Everything; // Default to printing everything
    public bool DafnyVerify = true;
    public string DafnyPrintResolvedFile = null;
    public List<string> DafnyPrintExportedViews = [];
    public bool Compile = true;
    public List<string> MainArgs = [];
    public bool FormatCheck = false;

    public string CompilerName;
    public IExecutableBackend Backend;
    public bool Verbose = true;
    public bool EnforcePrintEffects = false;
    public string DafnyPrintCompiledFile = null;
    public string CoverageLegendFile = null;
    public string MainMethod = null;
    public bool ForceCompile = false;
    public bool RunAfterCompile = false;
    public uint SpillTargetCode = 0; // [0..4]
    public bool DisallowIncludes = false;
    public bool DisallowExterns = false;
    public bool AllowExterns => !DisallowExterns;
    public bool DisableNLarith = false;
    public int ArithMode = 1; // [0..10]
    public string AutoReqPrintFile = null;
    public bool ignoreAutoReq = false;
    public bool Optimize = false;
    public bool AutoTriggers = true;
    public bool RewriteFocalPredicates = true;
    public bool PrintTooltips = false;
    public bool PrintStats = false;
    public string MethodsToTest = null;
    public bool DisallowConstructorCaseWithoutParentheses = false;
    public bool PrintFunctionCallGraph = false;
    public bool WarnShadowing = false;
    public FunctionSyntaxOptions FunctionSyntax = FunctionSyntaxOptions.Version4;
    public QuantifierSyntaxOptions QuantifierSyntax = QuantifierSyntaxOptions.Version4;

    public int DefiniteAssignmentLevel { get; set; } = 1;
    public HashSet<string> LibraryFiles { get; set; } = [];
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
    public bool IncludeRuntime = true;
    public CommonOptionBag.SystemModuleMode SystemModuleTranslationMode = CommonOptionBag.SystemModuleMode.Omit;
    public bool UseJavadocLikeDocstringRewriter = false;
    public bool DisableScopes = false;
    public bool UseStdin = false;
    public bool FailOnWarnings = false;
    [CanBeNull] private TestGenerationOptions testGenOptions = null;
    public bool ExtractCounterexample = false;

    public bool ShowProofObligationExpressions = false;

    public bool AuditProgram = false;

    public static string DefaultZ3Version = "4.12.1";
    // Not directly user-configurable, only recorded once we discover it
    public string SolverIdentifier { get; private set; }
    public Version SolverVersion { get; set; }

    public static readonly ReadOnlyCollection<Plugin> DefaultPlugins =
      new(new[] { SinglePassCodeGenerator.Plugin, InternalDocstringRewritersPluginConfiguration.Plugin });
    private IList<Plugin> cliPluginCache;
    public IList<Plugin> Plugins => cliPluginCache ??= ComputePlugins(AdditionalPlugins, AdditionalPluginArguments);
    public List<Plugin> AdditionalPlugins = [];
    public IList<string> AdditionalPluginArguments = new List<string>();

    public static IList<Plugin> ComputePlugins(List<Plugin> additionalPlugins, IList<string> allArguments) {
      var result = new List<Plugin>(DefaultPlugins.Concat(additionalPlugins));
      foreach (var pluginAndArgument in allArguments) {
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

    public static bool TryParseResourceCount(string value, out uint result) {
      return uint.TryParse(value, NumberStyles.AllowExponent, null, out result);
    }

    /// <summary>
    /// Automatic shallow-copy constructor
    /// </summary>
    public DafnyOptions(DafnyOptions src, bool useNullWriters = false) : this(
      src.Input, src.OutputWriter, src.ErrorWriter) {
      src.CopyTo(this, useNullWriters);
      CliRootSourceUris = new List<Uri>(src.CliRootSourceUris);
      ProverOptions = [.. src.ProverOptions];
      Options = new Options(
        src.Options.OptionArguments.ToDictionary(kv => kv.Key, kv => kv.Value),
        src.Options.Arguments.ToDictionary(kv => kv.Key, kv => kv.Value));
    }

    private void CopyTo(DafnyOptions dst, bool useNullWriters) {
      var type = typeof(DafnyOptions);
      while (type != null) {
        var fields = type.GetFields(BindingFlags.NonPublic | BindingFlags.Public | BindingFlags.Instance);
        foreach (var fi in fields) {
          var value = fi.GetValue(this);
          // This hacky code is necessary until we switch to a Boogie version that implements https://github.com/boogie-org/boogie/pull/788
          if (useNullWriters && fi.Name is "<ErrorWriter>k__BackingField" or "<OutputWriter>k__BackingField") {
            value = TextWriter.Null;
          }
          fi.SetValue(dst, value);
        }
        type = type.BaseType;
      }
    }

    public virtual TestGenerationOptions TestGenOptions =>
      testGenOptions ??= new TestGenerationOptions();

    public static void InvalidArgumentError(string name, Bpl.CommandLineParseState ps) {
      ps.Error("Invalid argument \"{0}\" to option {1}", ps.args[ps.i], name);
    }

    public override void ApplyDefaultOptions() {
      ApplyDefaultOptionsWithoutSettingsDefault();
    }

    public void ApplyDefaultOptionsWithoutSettingsDefault() {
      base.ApplyDefaultOptions();

      Backend ??= new CsharpBackend(this);
      // Ask Boogie to perform abstract interpretation
      UseAbstractInterpretation = true;
      Ai.J_Intervals = true;
    }

    public bool IsUsingZ3() {
      return !ProverOptions.Any(x => x.StartsWith("SOLVER=") && !x.EndsWith("=z3"));
    }

    public void ProcessSolverOptions(ErrorReporter errorReporter, IOrigin token) {
      if (IsUsingZ3()) {
        var z3Version = SetZ3ExecutablePath(errorReporter, token);
        SetZ3Options(z3Version);
      }
    }

    private static ConcurrentDictionary<string, Version> z3VersionPerPath = new();
    /// <summary>
    /// Dafny releases come with their own copy of Z3, to save users the trouble of having to install extra dependencies.
    /// For this to work, Dafny first tries any prover path explicitly provided by the user, then looks for for the copy
    /// distributed with Dafny, and finally looks in any directory in the system PATH environment variable.
    /// </summary>
    private Version SetZ3ExecutablePath(ErrorReporter errorReporter, IOrigin token) {
      string confirmedProverPath = null;
      string nextStepsMessage = $"Please either provide a path to the `z3` executable using the `--solver-path <path>` option, manually place the `z3` directory next to the `dafny` executable you are using (this directory should contain `bin/z3-{DefaultZ3Version}` or `bin/z3-{DefaultZ3Version}.exe`), or set the PATH environment variable to also include a directory containing the `z3` executable.";

      // Try an explicitly provided prover path, if there is one.
      var pp = "PROVER_PATH=";
      var proverPathOption = ProverOptions.Find(o => o.StartsWith(pp));
      if (proverPathOption != null) {
        var proverPath = proverPathOption.Substring(pp.Length);
        // Boogie will perform the ultimate test to see if "proverPath" is real--it will attempt to run it.
        // However, by at least checking if the file exists, we can produce a better error message in common scenarios.
        // Unfortunately, there doesn't seem to be a portable way of checking whether it's executable.
        if (!File.Exists(proverPath)) {
          errorReporter.Error(MessageSource.Verifier, token, $"Z3 not found at {proverPath}. " + nextStepsMessage);
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
        return z3VersionPerPath.GetOrAdd(confirmedProverPath, GetZ3Version);
      }

      errorReporter.Error(MessageSource.Verifier, DafnyProject.StartingToken, "Z3 is not found. " + nextStepsMessage);
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

    public void SetZ3Options(Version z3Version) {
      // Don't allow changing this once set, just in case:
      // a DooFile will record this and will get confused if it changes.
      if ((SolverIdentifier != null && SolverIdentifier != "Z3")
          || (SolverVersion != null && SolverVersion != z3Version)) {
        throw new Exception("Attempted to set Z3 options more than once");
      }
      SolverIdentifier = "Z3";
      SolverVersion = z3Version;

      // Boogie sets the following Z3 options by default:
      // smt.mbqi = false
      // model.compact = false
      // model.v2 = true
      // pp.bv_literals = false

      // Boogie also used to set the following options, but does not anymore.
      SetZ3Option("auto_config", "false");
      SetZ3Option("type_check", "true");
      SetZ3Option("smt.qi.eager_threshold", "44");
      SetZ3Option("smt.delay_units", "true");
      SetZ3Option("model_evaluator.completion", "true");
      SetZ3Option("model.completion", "true");
      if (z3Version is null || z3Version < new Version(4, 8, 6)) {
        SetZ3Option("model_compress", "false");
      } else {
        SetZ3Option("model.compact", "false");
      }

      // This option helps avoid "time travelling triggers".
      // See: https://github.com/dafny-lang/dafny/discussions/3362
      SetZ3Option("smt.case_split", "3");

      if (3 <= ArithMode) {
        SetZ3Option("smt.arith.nl", "false");
      }
    }
  }

  class ErrorReportingCommandLineParseState : Bpl.CommandLineParseState {
    private readonly Errors errors;
    private IOrigin token;

    public ErrorReportingCommandLineParseState(string[] args, string toolName, Errors errors, IOrigin token)
      : base(args, toolName) {
      this.errors = errors;
      this.token = token;
    }

    public override void Error(string message, params string[] args) {
      errors.SemErr(GenericErrors.ErrorId.g_option_error, token, string.Format(message, args));
      EncounteredErrors = true;
    }
  }

  /// <summary>
  /// Wrapper object that restricts which options may be applied.
  /// Used by the parser to parse <c>:options</c> strings.
  /// </summary>
  class DafnyAttributeOptions : DafnyOptions {
    public static readonly HashSet<string> KnownOptions = [
      "functionSyntax",
      "quantifierSyntax"
    ];

    private readonly Errors errors;
    public IOrigin Token { get; set; }

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
}
