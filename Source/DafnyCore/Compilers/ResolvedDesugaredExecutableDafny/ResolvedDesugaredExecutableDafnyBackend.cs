using System.Collections.Generic;
using System.IO;
using System.Text.RegularExpressions;

namespace Microsoft.Dafny.Compilers;

public class ResolvedDesugaredExecutableDafnyBackend : DafnyExecutableBackend {

  public override IReadOnlySet<string> SupportedExtensions => new HashSet<string> { ".dfy" };
  public override string TargetName => "ResolvedDesugaredExecutableDafny";
  public override bool IsStable => true;
  public override bool IsInternal => true;
  public override string TargetExtension => "dfy";
  public override bool SupportsInMemoryCompilation => false;
  public override bool TextualTargetIsExecutable => false;

  public override string TargetBaseDir(string dafnyProgramName) =>
    $"{Path.GetFileNameWithoutExtension(dafnyProgramName)}-ResolvedDesugaredExecutableDafny/src";

  protected override DafnyWrittenCompiler CreateDafnyWrittenCompiler() {
    return new ResolvedDesugaredExecutableDafnyCompiler();
  }

  public ResolvedDesugaredExecutableDafnyBackend(DafnyOptions options) : base(options) {
  }
}
