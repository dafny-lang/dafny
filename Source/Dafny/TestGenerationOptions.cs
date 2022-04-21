using System;
using JetBrains.Annotations;
using Bpl = Microsoft.Boogie;

namespace Microsoft.Dafny {

  public class TestGenerationOptions {

    public bool WarnDeadCode = false;
    public enum Modes { None, Block, Path };
    public Modes Mode = Modes.None;
    [CanBeNull] public string TargetMethod = null;
    public uint? SeqLengthLimit = null;
    public uint TestInlineDepth = 0;

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
              _ => throw new Exception("Invalid value for testMode")
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
    inlined.";

  }
}