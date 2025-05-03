using System.Collections.Generic;
using Microsoft.Dafny;
using Microsoft.Dafny.Compilers;

namespace DafnyCore.Backends.Lean;

public class LeanBackend : ExecutableBackend {
  public LeanBackend(DafnyOptions options) : base(options) { }
  public override IReadOnlySet<string> SupportedExtensions => new HashSet<string> { ".lean" };
  public override string TargetName => "Lean";
  public override bool IsStable => false;
  public override string TargetExtension => "lean";
  public override bool TextualTargetIsExecutable => false;
  public override bool SupportsInMemoryCompilation => false;
  protected override SinglePassCodeGenerator CreateCodeGenerator() {
    return new LeanCodeGenerator(Options, Reporter);
  }
}