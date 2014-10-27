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
    public DafnyOptions()
      : base("Dafny", "Dafny program verifier") {
    }

    public override string VersionNumber {
      get {
        return System.Diagnostics.FileVersionInfo.GetVersionInfo(System.Reflection.Assembly.GetExecutingAssembly().Location).FileVersion;
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

    public bool DisallowSoundnessCheating = false;
    public bool Dafnycc = false;
    public int Induction = 3;
    public int InductionHeuristic = 6;
    public string DafnyPrelude = null;
    public string DafnyPrintFile = null;
    public enum PrintModes { Everything, NoIncludes, NoGhost };
    public PrintModes PrintMode;
    public bool DafnyVerify = true;
    public string DafnyPrintResolvedFile = null;
    public bool Compile = true;
    public bool ForceCompile = false;
    public bool RunAfterCompile = false;
    public bool SpillTargetCode = false;
    public bool DisallowIncludes = false;
    public bool DisableNLarith = false;
    public string AutoReqPrintFile = null;
    public bool ignoreAutoReq = false;

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

        case "compile": {
            int compile = 0;
            if (ps.GetNumericArgument(ref compile, 4)) {
              // convert option to two booleans
              Compile = compile != 0;
              ForceCompile = compile == 2;
              RunAfterCompile = compile == 3;
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
            if (ps.GetNumericArgument(ref spill, 2)) {
              SpillTargetCode = spill != 0;  // convert to a boolean
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

        case "induction":
          ps.GetNumericArgument(ref Induction, 4);
          return true;

        case "inductionHeuristic":
          ps.GetNumericArgument(ref InductionHeuristic, 7);
          return true;

        case "noIncludes":
          DisallowIncludes = true;
          return true;

        case "noNLarith":
          DisableNLarith = true;
          this.Z3Options.Add("NL_ARITH=false");
          return true;

        case "autoReqPrint":
          if (ps.ConfirmArgumentCount(1)) {
              AutoReqPrintFile = args[ps.i];
          }
          return true;

        case "noAutoReq":
          ignoreAutoReq = true;
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
    }

    public override void AttributeUsage() {
      // TODO: provide attribute help here
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
  /printMode:<Everything|NoIncludes|NoGhost>
                NoIncludes disables printing of {:verify false} methods incorporated via the
                include mechanism, as well as datatypes and fields included from other files.
                NoGhost disables printing of functions, ghost methods, and proof statements in
                implementation methods.  It also disables anything NoIncludes disables.
  /rprint:<file>
                print Dafny program after resolving it
                (use - as <file> to print to console)
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
  /spillTargetCode:<n>
                0 (default) - don't write the compiled Dafny program (but
                    still compile it, if /compile indicates to do so)
                1 - write the compiled Dafny program as a .cs file
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
                    heuristically chosen quantifiers and ghost methods
  /inductionHeuristic:<n>
                0 - least discriminating induction heuristic (that is, lean
                    toward applying induction more often)
                1,2,3,4,5 - levels in between, ordered as follows as far as
                    how discriminating they are:  0 < 1 < 2 < (3,4) < 5 < 6
                6 (default) - most discriminating
  /noIncludes   Ignore include directives
  /noNLarith    Reduce Z3's knowledge of non-linear arithmetic (*,/,%). 
                Results in more manual work, but also produces more predictable behavior.
  /autoReqPrint:<file>
                Print out requirements that were automatically generated by autoReq.
  /noAutoReq    Ignore autoReq attributes
");
      base.Usage();  // also print the Boogie options
    }
  }
}
