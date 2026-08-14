using System;
using System.Collections.Generic;
using System.Diagnostics;
using JetBrains.Annotations;
using Bpl = Microsoft.Boogie;

namespace Microsoft.Dafny {

  public class TestGenerationOptions {
    public const string TestInlineAttribute = "testInline";
    public const string TestEntryAttribute = "testEntry";
    public bool WarnDeadCode = false;
    
    public bool Fdnf = false;
    public int? Bva;
    public bool Simplify = false;
    public uint Repeat = 1;
    public bool Time = false;
    public Stopwatch StopWatch;
    public HashSet<String> FailedVerification = [];
    
    public bool IgnoreWarnings = false;
    public enum Modes { None, Block, InlinedBlock, Path, Spec };
    public Modes Mode = Modes.None;
    public uint SeqLengthLimit = 0;
    [CanBeNull] public string PrintBpl = null;
    public bool ForcePrune = false;
    public string CoverageReport = null;
    public const uint DefaultTimeLimit = 20;
  }
}