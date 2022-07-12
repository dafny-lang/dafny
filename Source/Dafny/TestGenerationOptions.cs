using System;
using JetBrains.Annotations;
using Bpl = Microsoft.Boogie;

namespace Microsoft.Dafny {

  public class TestGenerationOptions {

    public bool WarnDeadCode = false;
    public enum Modes { None, Block, Path };
    public enum Oracles { None, Spec };
    public Modes Mode = Modes.None;
    public Oracles Oracle = Oracles.None;
    [CanBeNull] public string TargetMethod = null;
    public uint? SeqLengthLimit = null;
    public uint TestInlineDepth = 0;
    public uint Timeout = 100;
    public bool Verbose = false;
    public bool noPrune = false;
    [CanBeNull] public string PrintBpl = null;

    public bool ParseOption(string name, Bpl.CommandLineParseState ps) {
      var args = ps.args;

      switch (name) {

        case "warnDeadCode":
          WarnDeadCode = true;
          Mode = Modes.Block;
          return true;
        
        case "noPrune":
          noPrune = true;
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

        case "generateTestOracle":
          if (ps.ConfirmArgumentCount(1)) {
            Oracle = args[ps.i] switch {
              "None" => Oracles.None,
              "Spec" => Oracles.Spec,
              _ => throw new Exception("Invalid value for generateTestOracle")
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
        
        case "generateTestTimeout":
          var timeout = 0;
          if (ps.GetIntArgument(ref timeout)) {
            Timeout = (uint)timeout;
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
      }

      return false;
    }

    public string Help => @"
/generateTestMode:<None|Block|Path>
    None is the default and has no effect.
    Block prints block-coverage tests for the given program.
    Path prints path-coverage tests for the given program.
    Using /definiteAssignment:3 and /loopUnroll is highly recommended when
    generating tests.
    Please also consider using /prune, which generates more test at the cost
    of weaker test correctness guarantees
/generateTestOracle:<None|Spec>
    Determines the kind of oracles generated for the tests.
    None is the default and has no effect (the test contains no runtime checks).
    Spec asks the tool to generate runtime checks based on method specification
/warnDeadCode
    Use block-coverage tests to warn about potential dead code.
/generateTestSeqLengthLimit:<n>
    If /testMode is not None, using this argument adds an axiom that sets the
    length of all sequences to be no greater than <n>. This is useful in
    conjunction with loop unrolling.
/generateTestTargetMethod:<methodName>
    If specified, only this method will be tested.
/generateTestInlineDepth:<n>
    0 is the default. When used in conjunction with /testTargetMethod, this
    argument specifies the depth up to which all non-tested methods should be
    inlined.
/generateTestTimeout:<n>
    Timeout generation of a test for a particular block/path after n seconds
/generateTestPrintBpl:<fileName>
    Print the Boogie code after all transformations to a specified file
/generateTestVerbose
    Print various info as comments for debugging";

  }
}