using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Diagnostics.Contracts;
using Bpl = Microsoft.Boogie;

namespace Microsoft.Dafny
{
  public class DafnyOptions : Bpl.CommandLineOptions
  {
    private ErrorReporter errorReporter;

    public DafnyOptions(ErrorReporter errorReporter = null)
      : base("Dafny", "Dafny program verifier") {
        this.errorReporter = errorReporter;
        SetZ3ExecutableName();
    }

    public override string VersionNumber {
      get {
        return System.Diagnostics.FileVersionInfo.GetVersionInfo(System.Reflection.Assembly.GetExecutingAssembly().Location).FileVersion
#if ENABLE_IRONDAFNY
          + "[IronDafny]"
#endif
          ;
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
    public bool Dafnycc = false;
    public int Induction = 3;
    public int InductionHeuristic = 6;
    public bool TypeInferenceDebug = false;
    public string DafnyPrelude = null;
    public string DafnyPrintFile = null;
    public enum PrintModes { Everything, DllEmbed, NoIncludes, NoGhost };
    public PrintModes PrintMode = PrintModes.Everything;  // Default to printing everything
    public bool DafnyVerify = true;
    public string DafnyPrintResolvedFile = null;
    public List<string> DafnyPrintExportedViews = new List<string>();
    public bool Compile = true;
    [Flags]
    public enum CompilationTarget { Csharp = 1, JavaScript = 2, Go = 4, Java = 8 }
    public CompilationTarget CompileTarget = CompilationTarget.Csharp;
    public bool CompileVerbose = true;
    public string DafnyPrintCompiledFile = null;
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
    public bool IronDafny =
#if ENABLE_IRONDAFNY
      true
#else
      false
#endif
    ;

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

        case "dafnycc":
          Dafnycc = true;
          Induction = 0;
          Compile = false;
          UseAbstractInterpretation = false; // /noinfer
          return true;

        case "noCheating": {
            int cheat = 0; // 0 is default, allows cheating
            if (ps.GetNumericArgument(ref cheat, 2)) {
              DisallowSoundnessCheating = cheat == 1;
            }
            return true;
          }

        case "titrace":
          TypeInferenceDebug = true;
          return true;

        case "induction":
          ps.GetNumericArgument(ref Induction, 4);
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

        case "noIronDafny": {
            IronDafny = false;
            return true;
        }

        case "ironDafny": {
            IronDafny = true;
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
              DontShowLogo = true;
              DafnyVerify = false;
            }
          }
          return true;

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
      if (DisableNLarith || 3 <= ArithMode) {
        this.AddZ3Option("smt.arith.nl=false");
      }
    }

    public override void AttributeUsage() {
            Console.WriteLine(
@"Dafny: The following attributes are supported by this implementation.

    {:extern}
    {:extern <s1:string>}
    {:extern <s1:string>, <s2:string>}
      NOTE: :extern is target-language dependent.
      The extern modifier is used
        * to alter the CompileName of entities such as modules, classes, methods, etc.,
        * to alter the ReferenceName of the entities,
        * to decide whether to emit target code or not, and
        * to decide whether a declaration is allowed not to have a body.
      The CompileName is the name for the entity when translating to one of the target languages.
      The ReferenceName is the name used to refer to the entity in the target language.
      A common use case of :extern is to avoid name clashes with existing library functions.

      :extern takes 0, 1, or 2 (possibly empty) string arguments:
        - 0: Dafny will use the Dafny name as the CompileName and not affect the ReferenceName
        - 1: Dafny will use s1 as the CompileName, and replaces the last portion of the ReferenceName by s1.
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
      TODO

	{:tailrecursion}
      TODO

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
      TODO
");
    }


    /// <summary>
    /// Dafny comes with it's own copy of z3, to save new users the trouble of having to install extra dependency.
    /// For this to work, Dafny makes the Z3ExecutablePath point to the path were Z3 is put by our release script.
    /// For developers though (and people getting this from source), it's convenient to be able to run right away,
    /// so we vendor a Windows version.
    /// </summary>
    private void SetZ3ExecutableName() {
      var platform = (int)System.Environment.OSVersion.Platform;

      // http://www.mono-project.com/docs/faq/technical/
      var isUnix = platform == 4 || platform == 128;

      var z3binName = isUnix ? "z3" : "z3.exe";
      var dafnyBinDir = System.IO.Path.GetDirectoryName(System.Reflection.Assembly.GetExecutingAssembly().Location);
      var z3BinDir = System.IO.Path.Combine(dafnyBinDir, "z3", "bin");
      var z3BinPath = System.IO.Path.Combine(z3BinDir, z3binName);

      if (!System.IO.File.Exists(z3BinPath) && !isUnix) {
        // This is most likely a Windows user running from source without downloading z3
        // separately; this is ok, since we vendor z3.exe.
        z3BinPath = System.IO.Path.Combine(dafnyBinDir, z3binName);
      }

      if (!System.IO.File.Exists(z3BinPath) && errorReporter != null) {
        var tok = new Bpl.Token(1, 1) { filename = "*** " };
        errorReporter.Warning(MessageSource.Other, tok, "Could not find '{0}' in '{1}'.{2}Downloading and extracting a Z3 distribution to Dafny's 'Binaries' folder would solve this issue; for now, we'll rely on Boogie to find Z3.",
          z3binName, z3BinDir, System.Environment.NewLine);
      } else {
        Z3ExecutablePath = z3BinPath;
      }
    }

    public override void Usage() {
      Console.WriteLine(@"  ---- Dafny options ---------------------------------------------------------

  Multiple .dfy files supplied on the command line are concatenated into one
  Dafny program.

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
  /titrace      print type-inference debug info
  /view:<view1, view2>
                print the filtered views of a module after it is resolved (/rprint).
                if print before the module is resolved (/dprint), then everthing in the module is printed
                if no view is specified, then everything in the module is printed.

  /dafnyVerify:<n>
                0 - stop after typechecking
                1 - continue on to translation, verification, and compilation
  /compile:<n>  0 - do not compile Dafny program
                1 (default) - upon successful verification of the Dafny
                    program, compile Dafny program to .NET assembly
                    Program.exe (if the program has a Main method) or
                    Program.dll (othewise), where Program.dfy is the name
                    of the last .dfy file on the command line
                2 - always attempt to compile Dafny program to C# program
                    out.cs, regardless of verification outcome
                3 - if there is a Main method and there are no verification
                    errors, compiles program in memory (i.e., does not write
                    an output file) and runs it
                4 - like (3), but attempts to compile and run regardless of
                    verification outcome
  /compileTarget:<lang>
                cs (default) - Compilation to .NET via C#
                go - Compilation to Go
                js - Compilation to JavaScript
                java - Compilation to Java
  /compileVerbose:<n>
                0 - don't print status of compilation to the console
                1 (default) - print information such as files being written by
                    the compiler to the console
  /spillTargetCode:<n>
                0 (default) - don't write the compiled Dafny program (but
                    still compile it, if /compile indicates to do so)
                1 - write the compiled Dafny program as a .cs file, if it
                    is being compiled
                2 - write the compiled Dafny program as a .cs file, provided
                    it passes the verifier, regardless of /compile setting
                3 - write the compiled Dafny program as a .cs file, regardless
                    of verification outcome and /compile setting
                NOTE: If there are .cs or .dll files on the command line, then
                the compiled Dafny program will also be written. More precisely,
                such files on the command line implies /spillTargetCode:1 (or
                higher, if manually specified).
  /out:<file>
                filename and location for the generated .cs, .dll or .exe files
  /dafnycc      Disable features not supported by DafnyCC
  /noCheating:<n>
                0 (default) - allow assume statements and free invariants
                1 - treat all assumptions as asserts, and drop free.
  /induction:<n>
                0 - never do induction, not even when attributes request it
                1 - only apply induction when attributes request it
                2 - apply induction as requested (by attributes) and also
                    for heuristically chosen quantifiers
                3 (default) - apply induction as requested, and for
                    heuristically chosen quantifiers and lemmas
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
                0 - If preprocessing succeeds, set exit code to 0 regardless of the number
                    of verification errors.
                1 (default) - If preprocessing succeeds, set exit code to the number of
                              verification errors.
  /autoTriggers:<n>
                0 - Do not generate {:trigger} annotations for user-level quantifiers.
                1 (default) - Add a {:trigger} to each user-level quantifier. Existing
                              annotations are preserved.
  /rewriteFocalPredicates:<n>
                0 - Don't rewrite predicates in the body of prefix lemmas.
                1 (default) - In the body of prefix lemmas, rewrite any use of a focal predicate
                              P to P#[_k-1].
  /optimize     Produce optimized C# code, meaning:
                  - selects optimized C# prelude by passing
                    /define:DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE to csc.exe (requires
                    System.Collections.Immutable.dll in the source directory to successfully
                    compile).
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
                    not sound to be used with compilation
                1 (default) - enforces definite-assignment rules
                2 - enforces definite-assignment for all non-ghost non-yield-parameter
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
  /ironDafny    Enable experimental features needed to support Ironclad/Ironfleet. Use of
                these features may cause your code to become incompatible with future
                releases of Dafny.
  /noIronDafny  Disable Ironclad/Ironfleet features, if enabled by default.
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
");
      base.Usage();  // also print the Boogie options
    }
  }
}
