using System;
using JetBrains.Annotations;
using Bpl = Microsoft.Boogie;

namespace Microsoft.Dafny {

  public class TestGenerationOptions {

    public bool WarnDeadCode = false;
    public enum Modes { None, Block, Path };
    public Modes Mode = Modes.None;
    [CanBeNull] public string TargetMethod = null;
    public uint SeqLengthLimit = 0;
    public uint TestInlineDepth = 0;
    public bool Verbose = false;
    [CanBeNull] public string PrintBpl = null;
    [CanBeNull] public string PrintStats = null;
    public bool DisablePrune = false;
    public static readonly uint DefaultTimeLimit = 10;

    public bool ParseOption(string name, Bpl.CommandLineParseState ps) {
      var args = ps.args;

      switch (name) {

        case "warnDeadCode":
          WarnDeadCode = true;
          Mode = Modes.Block;
          return true;

        case "generateTestMode":
          if (ps.ConfirmArgumentCount(1)) {
            Mode = args[ps.i] switch {
              "None" => Modes.None,
              "Block" => Modes.Block,
              "Path" => Modes.Path,
              _ => throw new Exception("Invalid value for generateTestMode")
            };
          }
          return true;

        case "generateTestSeqLengthLimit":
          var limit = 0;
          if (ps.GetIntArgument(ref limit)) {
            SeqLengthLimit = (uint)limit;
          }
          return true;

        case "generateTestTargetMethod":
          if (ps.ConfirmArgumentCount(1)) {
            TargetMethod = args[ps.i];
          }
          return true;

        case "generateTestInlineDepth":
          var depth = 0;
          if (ps.GetIntArgument(ref depth)) {
            TestInlineDepth = (uint)depth;
          }
          return true;

        case "generateTestPrintBpl":
          if (ps.ConfirmArgumentCount(1)) {
            PrintBpl = args[ps.i];
          }
          return true;

        case "generateTestVerbose":
          Verbose = true;
          return true;

        case "generateTestNoPrune":
          DisablePrune = true;
          return true;
      }

      return false;
    }

    public string Help => @"
/warnDeadCode
    Use counterexample generation to warn about potential dead code.
/generateTestMode:<None|Block|Path>
    None (default) - Has no effect.
    Block - Prints block-coverage tests for the given program.
    Path - Prints path-coverage tests for the given program.
    Using /definiteAssignment:3, /generateTestNoPrune, 
    /generateTestSeqLengthLimit, and /loopUnroll is highly recommended
    when generating tests.
/generateTestSeqLengthLimit:<n>
    Add an axiom that sets the length of all sequences to be no greater 
    than <n>. 0 (default) indicates no limit.
/generateTestTargetMethod:<methodName>
    If specified, only this method will be tested.
/generateTestInlineDepth:<n>
    0 is the default. When used in conjunction with /testTargetMethod,
    this argument specifies the depth up to which all non-tested methods
    should be inlined.
/generateTestPrintBpl:<fileName>
    Print the Boogie code used during test generation.
/generateTestVerbose
    Print various debugging info as comments for the generated tests.
/generateTestNoPrune
    Disable axiom pruning that Dafny uses to speed up verification.";

  }
}
