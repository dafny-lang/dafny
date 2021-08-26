using System;
using JetBrains.Annotations;
using Bpl = Microsoft.Boogie;

namespace Microsoft.Dafny {

  /// <summary>
  /// An extension of DafnyOptions
  /// </summary>
  public class TestGenerationOptions : DafnyOptions {

    public enum Modes { None, Block, Path };
    public Modes Mode = Modes.None;
    [CanBeNull] public string TargetMethod = null;
    public uint? SeqLengthLimit = null;
    public uint TestInlineDepth = 0;

    public override TestGenerationOptions TestGenOptions => null;

    protected override bool ParseOption(string name, CommandLineParseState ps) {
      var args = ps.args;

      switch (name) {

        case "testMode":
          if (ps.ConfirmArgumentCount(1)) {
            Mode = args[ps.i] switch {
              "None" => Modes.None,
              "Block" => Modes.Block,
              "Path" => Modes.Path,
              _ => throw new Exception("Invalid value for testMode")
            };
          }
          return true;

        case "testSeqLengthLimit":
          var limit = 0;
          if (ps.GetNumericArgument(ref limit)) {
            SeqLengthLimit = (uint)limit;
          }
          return true;

        case "testTargetMethod":
          if (ps.ConfirmArgumentCount(1)) {
            TargetMethod = args[ps.i];
          }
          return true;

        case "testInlineDepth":
          var depth = 0;
          if (ps.GetNumericArgument(ref depth)) {
            TestInlineDepth = (uint)depth;
          }
          return true;
      }

      return false;
    }

    public override string Help => @"
/testMode:<None|Block|Path>
    None is the default and has no effect.
    Block prints block-coverage tests for the given program.
    Path prints path-coverage tests for the given program.
    Using \definiteAssignment:3 and \loopUnroll is highly recommended when
    generating tests.
/testSeqLengthLimit:<n>
    If \testMode is not None, using this argument adds an axiom that sets the
    length of all sequences to be no greater than <n>. This is useful in
    conjunction with loop unrolling.
/testTargetMethod:<methodName>
    If specified, only this method will be tested.
/testInlineDepth:<n>
    0 is the default. When used in conjunction with \testTargetMethod, this
    argument specifies the depth up to which all non-tested methods should be
    inlined.";

  }
}