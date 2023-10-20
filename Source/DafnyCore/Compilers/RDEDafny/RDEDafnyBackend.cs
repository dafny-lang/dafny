using System.Collections.Generic;
using System.IO;
using System.Text.RegularExpressions;

namespace Microsoft.Dafny.Compilers;

public class RDEDafnyBackend : DafnyExecutableBackend {

  public override IReadOnlySet<string> SupportedExtensions => new HashSet<string> { ".dfy" };
  public override string TargetName => "RDEDafny";
  public override bool IsStable => true;
  public override bool IsInternal => true;
  public override string TargetExtension => "dfy";
  public override bool SupportsInMemoryCompilation => false;
  public override bool TextualTargetIsExecutable => false;

  public override string TargetBaseDir(string dafnyProgramName) =>
    $"{Path.GetFileNameWithoutExtension(dafnyProgramName)}-rdedafny/src";

  protected override DafnyWrittenCompiler CreateDafnyWrittenCompiler() {
    return new RDEDafnyCompiler();
  }

  public RDEDafnyBackend(DafnyOptions options) : base(options) {
  }
}
