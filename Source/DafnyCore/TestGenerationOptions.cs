using System;
using JetBrains.Annotations;
using Bpl = Microsoft.Boogie;

namespace Microsoft.Dafny {

  public class TestGenerationOptions {
    public const string TestInlineAttribute = "testInline";
    public const string TestEntryAttribute = "testEntry";
    public bool WarnDeadCode = false;
    public enum Modes { None, Block, InlinedBlock, Path };
    public Modes Mode = Modes.None;
    public uint SeqLengthLimit = 0;
    [CanBeNull] public string PrintBpl = null;
    public bool ForcePrune = false;
    public string CoverageReport = null;
    public const uint DefaultTimeLimit = 20;
  }
}
