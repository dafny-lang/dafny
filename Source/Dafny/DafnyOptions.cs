// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Diagnostics.Contracts;
using System.IO;
using Bpl = Microsoft.Boogie;

namespace Microsoft.Dafny
{
  public class DafnyOptions : Bpl.CommandLineOptions
  {
    private ErrorReporter errorReporter;

    public DafnyOptions(ErrorReporter errorReporter = null)
      : base("Dafny", "Dafny program verifier") {
        this.errorReporter = errorReporter;
    }

    public override string VersionNumber {
      get {
        return System.Diagnostics.FileVersionInfo.GetVersionInfo(System.Reflection.Assembly.GetExecutingAssembly().Location).FileVersion;
      }
    }
    public override string Version {
      get {
        return ToolName + VersionSuffix;
      }
    }
    public override string VersionSuffix {
      get {
        return " " + VersionNumber;
      }
    }

    private static DafnyOptions clo;
    public static DafnyOptions O {
      get { return clo; }
    }

    public static void Install(DafnyOptions options) {
      Contract.Requires(options != null);
      clo = options;
      Bpl.CommandLineOptions.Install(options);
    }

    public bool UnicodeOutput = false;
    public bool DisallowSoundnessCheating = false;
    public int Induction = 4;
    public int InductionHeuristic = 6;
    public bool TypeInferenceDebug = false;
    public bool MatchCompilerDebug = false;
    public string DafnyPrelude = null;
    public string DafnyPrintFile = null;
    public enum PrintModes { Everything, DllEmbed, NoIncludes, NoGhost };
    public PrintModes PrintMode = PrintModes.Everything;  // Default to printing everything
    public bool DafnyVerify = true;
    public bool VerifyVerbose = true;
    public string DafnyPrintResolvedFile = null;
    public List<string> DafnyPrintExportedViews = new List<string>();
    public bool Compile = true;
    [Flags]
    public enum CompilationTarget { Csharp = 1, JavaScript = 2, Go = 4, Java = 8, Cpp = 16, Php = 32 }
    public CompilationTarget CompileTarget = CompilationTarget.Csharp;
    public bool CompileVerbose = true;
    public string DafnyPrintCompiledFile = null;
    public string CoverageLegendFile = null;
    public string MainMethod = null;
    public bool ForceCompile = false;
    public bool RunAfterCompile = false;
    public int SpillTargetCode = 0;  // [0..4]
    public bool DisallowIncludes = false;
    public bool DisallowExterns = false;
    public bool DisableNLarith = false;
    public int ArithMode = 1;  // [0..10]
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
    public int DefiniteAssignmentLevel = 1;  // [0..4]
    public bool ForbidNondeterminism {
      get { return DefiniteAssignmentLevel == 3; }
    }
    public int DeprecationNoise = 1;
    public bool VerifyAllModules = false;
    public bool SeparateModuleOutput = false;
    public enum IncludesModes { None, Immediate, Transitive }
    public IncludesModes PrintIncludesMode = IncludesModes.None;
    public int OptimizeResolution = 2;
    public bool UseRuntimeLib = false;
    public bool DisableScopes = false;
    public int Allocated = 3;
    public bool UseStdin = false;

    protected override bool ParseOption(string name, Bpl.CommandLineOptionEngine.CommandLineParseState ps) {
      var args = ps.args;  // convenient synonym

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
            }
            else if (args[ps.i].Equals("NoIncludes"))
            {
                PrintMode = PrintModes.NoIncludes;
            }
            else if (args[ps.i].Equals("NoGhost"))
            {
                PrintMode = PrintModes.NoGhost;
            }
            else if (args[ps.i].Equals("DllEmbed"))
            {
                PrintMode = PrintModes.DllEmbed;
            }
            else
            {
                throw new Exception("Invalid value for printMode");
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
            if (ps.GetNumericArgument(ref compile, 5)) {
              // convert option to two booleans
              Compile = compile != 0;
              ForceCompile = compile == 2 || compile == 4;
              RunAfterCompile = compile == 3 || compile == 4;
            }
            return true;
          }

        case "compileTarget":
          if (ps.ConfirmArgumentCount(1)) {
            if (args[ps.i].Equals("cs")) {
              CompileTarget = CompilationTarget.Csharp;
            } else if (args[ps.i].Equals("js")) {
              CompileTarget = CompilationTarget.JavaScript;
            } else if (args[ps.i].Equals("go")) {
              CompileTarget = CompilationTarget.Go;
            } else if (args[ps.i].Equals("java")) {
              CompileTarget = CompilationTarget.Java;
            } else if (args[ps.i].Equals("cpp")) {
              CompileTarget = CompilationTarget.Cpp;
            } else if (args[ps.i].Equals("php")) {
              CompileTarget = CompilationTarget.Php;
            } else {
              throw new Exception("Invalid value for compileTarget");
            }
          }
          return true;

        case "compileVerbose": {
          int verbosity = 0;
          if (ps.GetNumericArgument(ref verbosity, 2)) {
            CompileVerbose = verbosity == 1;
          }
          return true;
        }

        case "Main": case "main": {
          if (ps.ConfirmArgumentCount(1)) {
            MainMethod = args[ps.i];
          }
          return true;
        }

        case "dafnyVerify":
            {
                int verify = 0;
                if (ps.GetNumericArgument(ref verify, 2)) {
                    DafnyVerify = verify != 0; // convert to boolean
                }
                return true;
            }

        case "spillTargetCode": {
            int spill = 0;
            if (ps.GetNumericArgument(ref spill, 4)) {
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
            if (ps.GetNumericArgument(ref cheat, 2)) {
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
          ps.GetNumericArgument(ref Induction, 5);
          return true;

        case "inductionHeuristic":
          ps.GetNumericArgument(ref InductionHeuristic, 7);
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
            if (ps.GetNumericArgument(ref a, 11)) {
              ArithMode = a;
            }
            return true;
          }

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
          if (ps.GetNumericArgument(ref d, 3)) {
            DeprecationNoise = d;
          }
          return true;
        }

        case "countVerificationErrors": {
          int countErrors = 1; // defaults to reporting verification errors
          if (ps.GetNumericArgument(ref countErrors, 2)) {
            CountVerificationErrors = countErrors == 1;
          }
          return true;
        }

        case "printTooltips":
          PrintTooltips = true;
          return true;

        case "autoTriggers": {
            int autoTriggers = 0;
            if (ps.GetNumericArgument(ref autoTriggers, 2)) {
              AutoTriggers = autoTriggers == 1;
            }
            return true;
          }

        case "rewriteFocalPredicates": {
            int rewriteFocalPredicates = 0;
            if (ps.GetNumericArgument(ref rewriteFocalPredicates, 2)) {
              RewriteFocalPredicates = rewriteFocalPredicates == 1;
            }
            return true;
          }

        case "optimize": {
            Optimize = true;
            return true;
        }

        case "allocated": {
            ps.GetNumericArgument(ref Allocated, 5);
            return true;
        }

        case "optimizeResolution": {
            int d = 2;
            if (ps.GetNumericArgument(ref d, 3)) {
              OptimizeResolution = d;
            }
            return true;
          }

        case "definiteAssignment": {
            int da = 0;
            if (ps.GetNumericArgument(ref da, 4)) {
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
              throw new Exception("Invalid value for includesMode");
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

        default:
          break;
      }
      // not a Dafny-specific option, so defer to superclass
      return base.ParseOption(name, ps);
    }

    public override void ApplyDefaultOptions() {
      base.ApplyDefaultOptions();

      // expand macros in filenames, now that LogPrefix is fully determined
      ExpandFilename(ref DafnyPrelude, LogPrefix, FileTimestamp);
      ExpandFilename(ref DafnyPrintFile, LogPrefix, FileTimestamp);

      SetZ3ExecutablePath();
      SetZ3Options();

      // Ask Boogie to perform abstract interpretation
      UseAbstractInterpretation = true;
      Ai.J_Intervals = true;
    }

    public override string AttributeHelp =>
@"Dafny: The following attributes are supported by this version.

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

    {:axiom}
      TODO

    {:handle}
      TODO

    {:dllimport}
      TODO

    {:compile}
      TODO

    {:main}
      TODO

    {:axiom}
      TODO

    {:abstemious}
      TODO

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
      TODO

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
    private void SetZ3Option(string name, string value)
    {
      if (!ProverOptions.Any(o => o.StartsWith($"O:{name}=")))
      {
        ProverOptions.Add($"O:{name}={value}");
      }
    }

    private void SetZ3Options()
    {
      // Boogie sets the following Z3 options by default:
      // smt.mbqi = false
      // model.compact = false
      // model.v2 = true
      // pp.bv_literals = false

      // Boogie also used to set the following options, but does not anymore.
      SetZ3Option("auto_config", "false");
      SetZ3Option("type_check", "true");
      SetZ3Option("smt.case_split", "3");  // TODO: try removing
      SetZ3Option("smt.qi.eager_threshold", "100");  // TODO: try lowering
      SetZ3Option("smt.delay_units", "true");
      SetZ3Option("smt.arith.solver", "2");

      if (DisableNLarith || 3 <= ArithMode) {
        SetZ3Option("smt.arith.nl", "false");
      }
    }

    public override string Help =>
      base.Help +
@"

  ---- Dafny options ---------------------------------------------------------

 All the .dfy files supplied on the command line along with files recursively
 included by 'include' directives are considered a single Dafny program;
 however only those files listed on the command line are verified.

 Exit code: 0 -- success; 1 -- invalid command-line; 2 -- parse or type errors;
            3 -- compilation errors; 4 -- verification errors

/dprelude:<file>
    choose Dafny prelude file
/dprint:<file>
    print Dafny program after parsing it
    (use - as <file> to print to console)
/printMode:<Everything|DllEmbed|NoIncludes|NoGhost>
    Everything is the default.
    DllEmbed prints the source that will be included in a compiled dll.
    NoIncludes disables printing of {:verify false} methods incorporated via the
    include mechanism, as well as datatypes and fields included from other files.
    NoGhost disables printing of functions, ghost methods, and proof statements in
    implementation methods.  It also disables anything NoIncludes disables.
/rprint:<file>
    print Dafny program after resolving it
    (use - as <file> to print to console)
/pmtrace      print pattern-match compiler debug info
/titrace      print type-inference debug info
/view:<view1, view2>
    print the filtered views of a module after it is resolved (/rprint).
    If print before the module is resolved (/dprint), then everything in the module
    is printed.
    If no view is specified, then everything in the module is printed.

/dafnyVerify:<n>
    0 - stop after typechecking
    1 - continue on to translation, verification, and compilation
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
    cpp - Compilation to C++
    php - Compilation to PHP

    Note that the C++ backend has various limitations (see Docs/Compilation/Cpp.md).
    This includes lack of support for BigIntegers (aka int), most higher order
    functions, and advanced features like traits or co-inductive types.
/Main:<name>
    The (fully-qualified) name of the method to use as the executable entry point.
    Default is the method with the {:main} atrribute, or else the method named 'Main'.
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
/noIncludes   Ignore include directives
/noExterns    Ignore extern and dllimport attributes
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
/autoReqPrint:<file>
    Print out requirements that were automatically generated by autoReq.
/noAutoReq    Ignore autoReq attributes
/allowGlobals Allow the implicit class '_default' to contain fields, instance functions,
    and instance methods.  These class members are declared at the module scope,
    outside of explicit classes.  This command-line option is provided to simplify
    a transition from the behavior in the language prior to version 1.9.3, from
    which point onward all functions and methods declared at the module scope are
    implicitly static and fields declarations are not allowed at the module scope.
/countVerificationErrors:<n>
    [ deprecated ]
    0 - Set exit code to 0 regardless of the presence of any other errors.
    1 (default) - Emit usual exit code (cf. beginning of the help message).
/autoTriggers:<n>
    0 - Do not generate {:trigger} annotations for user-level quantifiers.
    1 (default) - Add a {:trigger} to each user-level quantifier. Existing
                  annotations are preserved.
/rewriteFocalPredicates:<n>
    0 - Don't rewrite predicates in the body of prefix lemmas.
    1 (default) - In the body of prefix lemmas, rewrite any use of a focal predicate
                  P to P#[_k-1].
/optimize     Produce optimized C# code, meaning:
      - passes /optimize flag to csc.exe.
/optimizeResolution:<n>
    0 - Resolve and translate all methods
    1 - Translate methods only in the call graph of current verification target
    2 (default) - As in 1, but only resolve method bodies in non-included Dafny sources
/stats        Print interesting statistics about the Dafny files supplied.
/funcCallGraph Print out the function call graph.  Format is: func,mod=callee*
/warnShadowing  Emits a warning if the name of a declared variable caused another variable
    to be shadowed
/definiteAssignment:<n>
    0 - ignores definite-assignment rules; this mode is for testing only--it is
        not sound
    1 (default) - enforces definite-assignment rules for variables and fields
        of types that do not support auto-initialization
    2 - enforces definite-assignment for all non-yield-parameter
        variables and fields, regardless of their types
    3 - like 2, but also performs checks in the compiler that no nondeterministic
        statements are used; thus, a program that passes at this level 3 is one
        that the language guarantees that values seen during execution will be
        the same in every run of the program
/deprecation:<n>
    0 - don't give any warnings about deprecated features
    1 (default) - show warnings about deprecated features
    2 - also point out where there's new simpler syntax
/verifyAllModules
    Verify modules that come from an include directive
/separateModuleOutput
    Output verification results for each module separately, rather than
    aggregating them after they are all finished.
/useRuntimeLib
    Refer to pre-built DafnyRuntime.dll in compiled assembly rather
    than including DafnyRuntime.cs verbatim.
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
/printTooltips
    Dump additional positional information (displayed as mouse-over tooltips by
    the VS plugin) to stdout as 'Info' messages.
/printIncludes:<None|Immediate|Transitive>
    None is the default.
    Immediate prints files included by files listed on the command line
    Transitive recurses on the files printed by Immediate
    Immediate and Transitive will exit after printing.
/disableScopes
    Treat all export sets as 'export reveal *'. i.e. don't hide function bodies
    or type definitions during translation.
/stdin
    Read standard input and treat it as an input .dfy file.

Dafny generally accepts Boogie options and passes these on to Boogie. However,
some Boogie options, like /loopUnroll, may not be sound for Dafny or may not
have the same meaning for a Dafny program as it would for a similar Boogie
program.";
  }
}
