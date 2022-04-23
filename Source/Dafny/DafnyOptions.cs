// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

using System;
using System.Collections.Generic;
using System.Collections.ObjectModel;
using System.Linq;
using System.Diagnostics.Contracts;
using System.IO;
using System.Text.RegularExpressions;
using JetBrains.Annotations;
using Microsoft.Dafny.Compilers;
using Microsoft.Dafny.Plugins;
using Bpl = Microsoft.Boogie;

namespace Microsoft.Dafny {
  public class DafnyOptions : Bpl.CommandLineOptions {

    public static DafnyOptions Create(params string[] arguments) {
      var result = new DafnyOptions();
      result.Parse(arguments);
      return result;
    }

    public DafnyOptions()
      : base("Dafny", "Dafny program verifier", new DafnyConsolePrinter()) {
      Prune = true;
      NormalizeNames = true;
      EmitDebugInformation = false;
      Compiler = new CsharpCompiler();
    }

    public override string VersionNumber {
      get {
        return System.Diagnostics.FileVersionInfo
          .GetVersionInfo(System.Reflection.Assembly.GetExecutingAssembly().Location).FileVersion;
      }
    }

    public override string Version {
      get { return ToolName + VersionSuffix; }
    }

    public override string VersionSuffix {
      get { return " " + VersionNumber; }
    }

    private static DafnyOptions clo;

    public static DafnyOptions O {
      get { return clo; }
    }

    public static void Install(DafnyOptions options) {
      Contract.Requires(options != null);
      clo = options;
    }

    public bool UnicodeOutput = false;
    public bool DisallowSoundnessCheating = false;
    public int Induction = 4;
    public int InductionHeuristic = 6;
    public bool TypeInferenceDebug = false;
    public bool MatchCompilerDebug = false;
    public string DafnyPrelude = null;
    public string DafnyPrintFile = null;

    public enum PrintModes {
      Everything,
      DllEmbed,
      NoIncludes,
      NoGhost
    }

    public PrintModes PrintMode = PrintModes.Everything; // Default to printing everything
    public bool DafnyVerify = true;
    public string DafnyPrintResolvedFile = null;
    public List<string> DafnyPrintExportedViews = new List<string>();
    public bool Compile = true;

    public Compiler Compiler;
    public bool CompileVerbose = true;
    public bool EnforcePrintEffects = false;
    public string DafnyPrintCompiledFile = null;
    public string CoverageLegendFile = null;
    public string MainMethod = null;
    public bool RunAllTests = false;
    public bool ForceCompile = false;
    public bool RunAfterCompile = false;
    public int SpillTargetCode = 0; // [0..4]
    public bool DisallowIncludes = false;
    public bool DisallowExterns = false;
    public bool DisableNLarith = false;
    public int ArithMode = 1; // [0..10]
    public string AutoReqPrintFile = null;
    public bool ignoreAutoReq = false;
    public bool AllowGlobals = false;
    public bool CountVerificationErrors = true;
    public bool Optimize = false;
    public bool AutoTriggers = true;
    public bool RewriteFocalPredicates = true;
    public bool PrintTooltips = false;
    public bool PrintStats = false;
    public bool PrintFunctionCallGraph = false;
    public bool WarnShadowing = false;
    public int DefiniteAssignmentLevel = 1; // [0..4]
    public FunctionSyntaxOptions FunctionSyntax = FunctionSyntaxOptions.Version3;

    public enum FunctionSyntaxOptions {
      Version3,
      Migration3To4,
      ExperimentalTreatUnspecifiedAsGhost,
      ExperimentalTreatUnspecifiedAsCompiled,
      ExperimentalPredicateAlwaysGhost,
      Version4,
    }

    public bool ForbidNondeterminism {
      get { return DefiniteAssignmentLevel == 3; }
    }

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
    public int Allocated = 3;
    public bool UseStdin = false;
    public bool ShowSnippets = false;
    public bool WarningsAsErrors = false;
    [CanBeNull] private TestGenerationOptions testGenOptions = null;
    public bool ExtractCounterexample = false;
    public List<string> VerificationLoggerConfigs = new();
    // Working around the fact that xmlFilename is private
    public string BoogieXmlFilename = null;

    public static readonly ReadOnlyCollection<Plugin> DefaultPlugins = new(new[] { Compilers.SinglePassCompiler.Plugin });
    public List<Plugin> Plugins = new(DefaultPlugins);

    public virtual TestGenerationOptions TestGenOptions =>
      testGenOptions ??= new TestGenerationOptions();

    protected override bool ParseOption(string name, Bpl.CommandLineParseState ps) {
      var args = ps.args; // convenient synonym
      switch (name) {
        case "dprelude":
          if (ps.ConfirmArgumentCount(1)) {
            DafnyPrelude = args[ps.i];
          }

          return true;

        case "dprint":
          if (ps.ConfirmArgumentCount(1)) {
            DafnyPrintFile = args[ps.i];
          }

          return true;

        case "printMode":
          if (ps.ConfirmArgumentCount(1)) {
            if (args[ps.i].Equals("Everything")) {
              PrintMode = PrintModes.Everything;
            } else if (args[ps.i].Equals("NoIncludes")) {
              PrintMode = PrintModes.NoIncludes;
            } else if (args[ps.i].Equals("NoGhost")) {
              PrintMode = PrintModes.NoGhost;
            } else if (args[ps.i].Equals("DllEmbed")) {
              PrintMode = PrintModes.DllEmbed;
            } else {
              InvalidArgumentError(name, ps);
            }
          }

          return true;

        case "rprint":
          if (ps.ConfirmArgumentCount(1)) {
            DafnyPrintResolvedFile = args[ps.i];
          }

          return true;
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

        case "compileTarget":
          if (ps.ConfirmArgumentCount(1)) {
            var compileTarget = args[ps.i];
            var compilers = Plugins.SelectMany(p => p.GetCompilers()).ToList();
            Compiler = compilers.LastOrDefault(c => c.TargetId == compileTarget);
            if (Compiler == null) {
              var known = String.Join(", ", compilers.Select(c => $"'{c.TargetId}' ({c.TargetLanguage})"));
              ps.Error($"No compiler found for compileTarget \"{compileTarget}\"; expecting one of {known}");
            }
          }

          return true;

        case "compileVerbose": {
            int verbosity = 0;
            if (ps.GetIntArgument(ref verbosity, 2)) {
              CompileVerbose = verbosity == 1;
            }

            return true;
          }

        case "Plugin":
        case "plugin": {
            if (ps.ConfirmArgumentCount(1)) {
              var pluginAndArgument = args[ps.i];
              if (pluginAndArgument.Length > 0) {
                var pluginArray = pluginAndArgument.Split(',');
                var pluginPath = pluginArray[0];
                var arguments = Array.Empty<string>();
                if (pluginArray.Length >= 2) {
                  // There are no commas in paths, but there can be in arguments
                  var argumentsString = string.Join(',', pluginArray.Skip(1));
                  // Parse arguments, accepting and remove double quotes that isolate long arguments
                  arguments = ParsePluginArguments(argumentsString);
                }
                Plugins.Add(AssemblyPlugin.Load(pluginPath, arguments));
              }
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

        case "spillTargetCode": {
            int spill = 0;
            if (ps.GetIntArgument(ref spill, 4)) {
              SpillTargetCode = spill;
            }

            return true;
          }
        case "out": {
            if (ps.ConfirmArgumentCount(1)) {
              DafnyPrintCompiledFile = args[ps.i];
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

        case "pmtrace":
          MatchCompilerDebug = true;
          return true;

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

        case "countVerificationErrors": {
            int countErrors = 1; // defaults to reporting verification errors
            if (ps.GetIntArgument(ref countErrors, 2)) {
              CountVerificationErrors = countErrors == 1;
            }

            return true;
          }

        case "printTooltips":
          PrintTooltips = true;
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
            if (ps.GetIntArgument(ref da, 4)) {
              DefiniteAssignmentLevel = da;
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

        case "showSnippets": {
            if (ps.ConfirmArgumentCount(1)) {
              if (args[ps.i].Equals("0")) {
                ShowSnippets = false;
              } else if (args[ps.i].Equals("1")) {
                ShowSnippets = true;
              } else {
                InvalidArgumentError(name, ps);
              }
            }

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

      }

      // Unless this is an option for test generation, defer to superclass
      return TestGenOptions.ParseOption(name, ps) || base.ParseOption(name, ps);
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

    protected void InvalidArgumentError(string name, Bpl.CommandLineParseState ps) {
      ps.Error("Invalid argument \"{0}\" to option {1}", ps.args[ps.i], name);
    }

    public override void ApplyDefaultOptions() {
      base.ApplyDefaultOptions();

      if (VerificationLoggerConfigs.Any()) {
        if (XmlSink != null) {
          throw new Exception("The /verificationLogger and /xml options cannot be used at the same time.");
        }

        BoogieXmlFilename = Path.GetTempFileName();
        XmlSink = new Bpl.XmlSink(this, BoogieXmlFilename);
      }

      Compiler ??= new CsharpCompiler();

      // expand macros in filenames, now that LogPrefix is fully determined
      ExpandFilename(DafnyPrelude, x => DafnyPrelude = x, LogPrefix, FileTimestamp);
      ExpandFilename(DafnyPrintFile, x => DafnyPrintFile = x, LogPrefix, FileTimestamp);

      SetZ3ExecutablePath();
      SetZ3Options();

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
      TODO

    {:main}
      TODO

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

    {:warnShadowing}
      TODO

    {:verify}
      TODO

    {:autocontracts}
      TODO

    {:opaque}
      TODO

    {:autoReq}
      TODO

    {:timeLimitMultiplier}
      TODO

    {:no_inline}
      TODO

    {:nowarn}
      TODO

    {:autotriggers}
      TODO

    {:trigger}
      TODO";

    /// <summary>
    /// Dafny releases come with their own copy of Z3, to save users the trouble of having to install extra dependencies.
    /// For this to work, Dafny looks for Z3 at the location where it is put by our release script (i.e., z3/bin/z3[.exe]).
    /// If Z3 is not found there, Dafny relies on Boogie to locate Z3 (which also supports setting a path explicitly on the command line).
    /// Developers (and people getting Dafny from source) need to install an appropriate version of Z3 themselves.
    /// </summary>
    private void SetZ3ExecutablePath() {
      var pp = "PROVER_PATH=";
      var proverPathOption = ProverOptions.Find(o => o.StartsWith(pp));
      if (proverPathOption != null) {
        var proverPath = proverPathOption.Substring(pp.Length);
        // Boogie will perform the ultimate test to see if "proverPath" is real--it will attempt to run it.
        // However, by at least checking if the file exists, we can produce a better error message in common scenarios.
        if (!File.Exists(proverPath)) {
          throw new Bpl.ProverException($"Requested prover not found: '{proverPath}'");
        }
      } else {
        var platform = (int)System.Environment.OSVersion.Platform;

        var isUnix = platform == 4 || platform == 6 || platform == 128;

        var z3binName = isUnix ? "z3" : "z3.exe";
        var dafnyBinDir = System.IO.Path.GetDirectoryName(System.Reflection.Assembly.GetExecutingAssembly().Location);
        var z3BinDir = System.IO.Path.Combine(dafnyBinDir, "z3", "bin");
        var z3BinPath = System.IO.Path.Combine(z3BinDir, z3binName);

        if (System.IO.File.Exists(z3BinPath)) {
          // Let's use z3BinPath
          ProverOptions.Add($"{pp}{z3BinPath}");
        }
      }
    }

    // Set a Z3 option, but only if it is not overwriting an existing option.
    private void SetZ3Option(string name, string value) {
      if (!ProverOptions.Any(o => o.StartsWith($"O:{name}="))) {
        ProverOptions.Add($"O:{name}={value}");
      }
    }

    private void SetZ3Options() {
      // Boogie sets the following Z3 options by default:
      // smt.mbqi = false
      // model.compact = false
      // model.v2 = true
      // pp.bv_literals = false

      // Boogie also used to set the following options, but does not anymore.
      SetZ3Option("auto_config", "false");
      SetZ3Option("type_check", "true");
      SetZ3Option("smt.case_split", "3"); // TODO: try removing
      SetZ3Option("smt.qi.eager_threshold", "100"); // TODO: try lowering
      SetZ3Option("smt.delay_units", "true");
      SetZ3Option("smt.arith.solver", "2");

      if (DisableNLarith || 3 <= ArithMode) {
        SetZ3Option("smt.arith.nl", "false");
      }
    }

    protected override string HelpBody =>
      $@"
All the .dfy files supplied on the command line along with files recursively
included by 'include' directives are considered a single Dafny program;
however only those files listed on the command line are verified.

Exit code: 0 -- success; 1 -- invalid command-line; 2 -- parse or type errors;
           3 -- compilation errors; 4 -- verification errors

---- Input configuration ---------------------------------------------------

/dprelude:<file>
    choose Dafny prelude file
/stdin
    Read standard input and treat it as an input .dfy file.

---- Plugins ---------------------------------------------------------------

/plugin:<path to one assembly>[ <arguments>]
    (experimental) One path to an assembly that contains at least one
    instantiatable class extending Microsoft.Dafny.Plugin.Rewriter.
    It can also extend Microsoft.Dafny.Plugins.PluginConfiguration to receive arguments
    More information about what plugins do and how define them:
    https://github.com/dafny-lang/dafny/blob/master/Source/DafnyLanguageServer/README.md#about-plugins

---- Overall reporting and printing ----------------------------------------

/stats        Print interesting statistics about the Dafny files supplied.
/dprint:<file>
    print Dafny program after parsing it
    (use - as <file> to print to console)
/rprint:<file>
    print Dafny program after resolving it
    (use - as <file> to print to console)
/printMode:<Everything|DllEmbed|NoIncludes|NoGhost>
    Everything is the default.
    DllEmbed prints the source that will be included in a compiled dll.
    NoIncludes disables printing of {{:verify false}} methods incorporated via the
    include mechanism, as well as datatypes and fields included from other files.
    NoGhost disables printing of functions, ghost methods, and proof statements in
    implementation methods.  It also disables anything NoIncludes disables.
/printIncludes:<None|Immediate|Transitive>
    None is the default.
    Immediate prints files included by files listed on the command line
    Transitive recurses on the files printed by Immediate
    Immediate and Transitive will exit after printing.
/view:<view1, view2>
    print the filtered views of a module after it is resolved (/rprint).
    If print before the module is resolved (/dprint), then everything in the module
    is printed.
    If no view is specified, then everything in the module is printed.
/showSnippets:<n>
    0 (default) - don't show source code snippets for Dafny messages
    1 - show a source code snippet for each Dafny message
/funcCallGraph Print out the function call graph.  Format is: func,mod=callee*
/pmtrace      print pattern-match compiler debug info
/titrace      print type-inference debug info
/printTooltips
    Dump additional positional information (displayed as mouse-over tooltips by
    the VS plugin) to stdout as 'Info' messages.

---- Language feature selection --------------------------------------------

/noIncludes   Ignore include directives
/noExterns    Ignore extern and dllimport attributes
/functionSyntax:<version>
    The syntax for functions is changing from Dafny version 3 to version 4.
    This switch gives early access to the new syntax, and also provides a mode
    to help with migration.
    3 (default) - Compiled functions are written `function method` and
        `predicate method`. Ghost functions are written `function` and `predicate`.
    4 - Compiled functions are written `function` and `predicate`. Ghost functions
        are written `ghost function` and `ghost predicate`.
    migration3to4 - Compiled functions are written `function method` and
        `predicate method`. Ghost functions are written `ghost function` and
        `ghost predicate`. To migrate from version 3 to version 4, use this flag
        on your version 3 program. This will give flag all occurrences of
        `function` and `predicate` as parsing errors. These are ghost functions,
        so change those into the new syntax `ghost function` and `ghost predicate`.
        Then, start using /functionSyntax:4. This will flag all occurrences of
        `function method` and `predicate method` as parsing errors. So, change
        those to just `function` and `predicate`. Now, your program uses version 4
        syntax and has the exact same meaning as your previous version 3 program.
    experimentalDefaultGhost - like migration3to4, but allow `function` and
        `predicate` as alternatives to declaring ghost functions and predicates,
        respectively
    experimentalDefaultCompiled - like migration3to4, but allow `function` and
        `predicate` as alternatives to declaring compiled functions and predicates,
        respectively
    experimentalPredicateAlwaysGhost - Compiled functions are written `function`.
        Ghost functions are written `ghost function`. Predicates are always ghost
        and are written `predicate`.
/disableScopes
    Treat all export sets as 'export reveal *'. i.e. don't hide function bodies
    or type definitions during translation.
/allowGlobals Allow the implicit class '_default' to contain fields, instance functions,
    and instance methods.  These class members are declared at the module scope,
    outside of explicit classes.  This command-line option is provided to simplify
    a transition from the behavior in the language prior to version 1.9.3, from
    which point onward all functions and methods declared at the module scope are
    implicitly static and fields declarations are not allowed at the module scope.

---- Warning selection -----------------------------------------------------

/warnShadowing  Emits a warning if the name of a declared variable caused another variable
    to be shadowed
/deprecation:<n>
    0 - don't give any warnings about deprecated features
    1 (default) - show warnings about deprecated features
    2 - also point out where there's new simpler syntax
/warningsAsErrors
    Treat warnings as errors.

---- Verification options -------------------------------------------------

/dafnyVerify:<n>
    0 - stop after typechecking
    1 - continue on to translation, verification, and compilation
/verifyAllModules
    Verify modules that come from an include directive
/separateModuleOutput
    Output verification results for each module separately, rather than
    aggregating them after they are all finished.
/verificationLogger:<configuration string>
    Logs verification results to the given test result logger. The currently
    supported loggers are `trx`, `csv`, and `text`. These are the
    XML-based format commonly used for test results for .NET languages, a
    custom CSV schema, and a textual format meant for human consumption. You
    can provide configuration using the same string format as when using the
    --logger option for dotnet test, such as:
        /verificationLogger:trx;LogFileName=<...>.
    The exact mapping of verification concepts to these formats is
    experimental and subject to change!

    The `trx` and `csv` loggers automatically choose an output file
    name by default, and print the name of this file to the console. The
    `text` logger prints its output to the console by default, but can
    send output to a file given the `LogFileName` option.

    The `text` logger also includes a more detailed breakdown of what
    assertions appear in each assertion batch. When combined with the
    `/vcsSplitOnEveryAssert` option, it will provide approximate time
    and resource use costs for each assertion, allowing identification
    of especially expensive assertions.
/mimicVerificationOf:<Dafny version>
    Let Dafny attempt to mimic the verification as it was in a previous version of Dafny.
    Useful during migration to a newer version of Dafny when a Dafny program has proofs, such as methods or lemmas,
    that are unstable in the sense that their verification may become slower or fail altogether
    after logically irrelevant changes are made in the verification input.

    Accepted versions are: 3.3 (note that this turns off features that prevent classes of verification instability)
/noCheating:<n>
    0 (default) - allow assume statements and free invariants
    1 - treat all assumptions as asserts, and drop free.
/induction:<n>
    0 - never do induction, not even when attributes request it
    1 - only apply induction when attributes request it
    2 - apply induction as requested (by attributes) and also
        for heuristically chosen quantifiers
    3 - apply induction as requested, and for
        heuristically chosen quantifiers and lemmas
    4 (default) - apply induction as requested, and for lemmas
/inductionHeuristic:<n>
    0 - least discriminating induction heuristic (that is, lean
        toward applying induction more often)
    1,2,3,4,5 - levels in between, ordered as follows as far as
        how discriminating they are:  0 < 1 < 2 < (3,4) < 5 < 6
    6 (default) - most discriminating
/trackPrintEffects:<n>
    0 (default) - Every compiled method, constructor, and iterator, whether or not
       it bears a {{:print}} attribute, may have print effects.
    1 - A compiled method, constructor, or iterator is allowed to have print effects
       only if it is marked with {{:print}}.
/allocated:<n>
    Specify defaults for where Dafny should assert and assume
    allocated(x) for various parameters x, local variables x,
    bound variables x, etc.  Lower <n> may require more manual
    allocated(x) annotations and thus may be more difficult to use.
    Warning: this option should be chosen consistently across
    an entire project; it would be unsound to use different
    defaults for different files or modules within a project.
    And even so, modes /allocated:0 and /allocated:1 let functions
    depend on the allocation state, which is not sound in general.
    0 - Nowhere (never assume/assert allocated(x) by default).
    1 - Assume allocated(x) only for non-ghost variables and fields
        (these assumptions are free, since non-ghost variables
        always contain allocated values at run-time).  This option
        may speed up verification relative to /allocated:2.
    2 - Assert/assume allocated(x) on all variables,
        even bound variables in quantifiers.  This option is
        the easiest to use for heapful code.
    3 - (default) Frugal use of heap parameters.
    4 - mode 3 but with alloc antecedents when ranges don't imply
        allocatedness.
/definiteAssignment:<n>
    0 - ignores definite-assignment rules; this mode is for testing only--it is
        not sound
    1 (default) - enforces definite-assignment rules for compiled variables and fields
        whose types do not support auto-initialization and for ghost variables
        and fields whose type is possibly empty
    2 - enforces definite-assignment for all non-yield-parameter
        variables and fields, regardless of their types
    3 - like 2, but also performs checks in the compiler that no nondeterministic
        statements are used; thus, a program that passes at this level 3 is one
        that the language guarantees that values seen during execution will be
        the same in every run of the program
/noAutoReq    Ignore autoReq attributes
/autoReqPrint:<file>
    Print out requirements that were automatically generated by autoReq.
/noNLarith    Reduce Z3's knowledge of non-linear arithmetic (*,/,%).
    Results in more manual work, but also produces more predictable behavior.
    (This switch will perhaps be replaced by /arith in the future.
    For now, it takes precedence of /arith.)
/arith:<n>    (Experimental switch. Its options may change.)
    0 - Use Boogie/Z3 built-ins for all arithmetic operations.
    1 (default) - Like 0, but introduce symbolic synonyms for *,/,%, and
        allow these operators to be used in triggers.
    2 - Like 1, but introduce symbolic synonyms also for +,-.
    3 - Turn off non-linear arithmetic in the SMT solver. Still,
        use Boogie/Z3 built-in symbols for all arithmetic operations.
    4 - Like 3, but introduce symbolic synonyms for *,/,%, and allow these
        operators to be used in triggers.
    5 - Like 4, but introduce symbolic synonyms also for +,-.
    6 - Like 5, and introduce axioms that distribute + over *.
    7 - like 6, and introduce facts that associate literals arguments of *.
    8 - Like 7, and introduce axiom for the connection between *,/,%.
    9 - Like 8, and introduce axioms for sign of multiplication
    10 - Like 9, and introduce axioms for commutativity and
        associativity of *
/autoTriggers:<n>
    0 - Do not generate {{:trigger}} annotations for user-level quantifiers.
    1 (default) - Add a {{:trigger}} to each user-level quantifier. Existing
                  annotations are preserved.
/rewriteFocalPredicates:<n>
    0 - Don't rewrite predicates in the body of prefix lemmas.
    1 (default) - In the body of prefix lemmas, rewrite any use of a focal predicate
                  P to P#[_k-1].
/extractCounterexample
    If verification fails, report a detailed counterexample for the first
    failing assertion. Requires specifying the /mv option as well as
    /proverOpt:O:model_compress=false and /proverOpt:O:model.completion=true.
/countVerificationErrors:<n>
    [ deprecated ]
    0 - Set exit code to 0 regardless of the presence of any other errors.
    1 (default) - Emit usual exit code (cf. beginning of the help message).

---- Test generation options -----------------------------------------------

{TestGenOptions.Help}

---- Compilation options ---------------------------------------------------

/compile:<n>  0 - do not compile Dafny program
    1 (default) - upon successful verification of the Dafny
        program, compile it to the designated target language
        (/noVerify automatically counts as failed verification)
    2 - always attempt to compile Dafny program to the target
        language, regardless of verification outcome
    3 - if there is a Main method and there are no verification
        errors and /noVerify is not used, compiles program in
        memory (i.e., does not write an output file) and runs it
    4 - like (3), but attempts to compile and run regardless of
        verification outcome
/compileTarget:<lang>
    cs (default) - Compilation to .NET via C#
    go - Compilation to Go
    js - Compilation to JavaScript
    java - Compilation to Java
    py - Compilation to Python
    cpp - Compilation to C++

    Note that the C++ backend has various limitations (see Docs/Compilation/Cpp.md).
    This includes lack of support for BigIntegers (aka int), most higher order
    functions, and advanced features like traits or co-inductive types.
/Main:<name>
    The (fully-qualified) name of the method to use as the executable entry point.
    Default is the method with the {{:main}} attribute, or else the method named 'Main'.
/runAllTests:<n> (experimental)
    0 (default) - Annotates compiled methods with the {{:test}} attribute
        such that they can be tested using a testing framework
        in the target language (e.g. xUnit for C#).
    1 - Emits a main method in the target language that will execute every method
        in the program with the {{:test}} attribute.
        Cannot be used if the program already contains a main method.
        Note that /compile:3 or 4 must be provided as well to actually execute
        this main method!
/compileVerbose:<n>
    0 - don't print status of compilation to the console
    1 (default) - print information such as files being written by
        the compiler to the console
/spillTargetCode:<n>
    This option concerns the textual representation of the target program.
    This representation is of no interest when working with only Dafny code,
    but may be of interest in cross-language situations.
    0 (default) - Don't make any extra effort to write the textual target program
        (but still compile it, if /compile indicates to do so).
    1 - Write the textual target program, if it is being compiled.
    2 - Write the textual target program, provided it passes the verifier (and
        /noVerify is NOT used), regardless of /compile setting.
    3 - Write the textual target program, regardless of verification outcome
        and /compile setting.
    Note, some compiler targets may (always or in some situations) write out the
    textual target program as part of compilation, in which case /spillTargetCode:0
    behaves the same way as /spillTargetCode:1.
/out:<file>
    filename and location for the generated target language files
/coverage:<file>
    The compiler emits branch-coverage calls and outputs into
    <file> a legend that gives a description of each
    source-location identifier used in the branch-coverage calls.
    (use - as <file> to print to console)
/optimize     Produce optimized C# code, meaning:
      - passes /optimize flag to csc.exe.
/optimizeResolution:<n>
    0 - Resolve and translate all methods
    1 - Translate methods only in the call graph of current verification target
    2 (default) - As in 1, but only resolve method bodies in non-included Dafny sources
/useRuntimeLib
    Refer to pre-built DafnyRuntime.dll in compiled assembly rather
    than including DafnyRuntime.cs verbatim.

----------------------------------------------------------------------------

Dafny generally accepts Boogie options and passes these on to Boogie. However,
some Boogie options, like /loopUnroll, may not be sound for Dafny or may not
have the same meaning for a Dafny program as it would for a similar Boogie
program.
".Replace("\n", "\n  ") + base.HelpBody;
  }
}
