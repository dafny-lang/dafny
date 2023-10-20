using System.Collections.Generic;
using System.IO;
using System.Text.RegularExpressions;

namespace Microsoft.Dafny.Compilers;

public class FDafnyBackend : DafnyExecutableBackend {

  public override IReadOnlySet<string> SupportedExtensions => new HashSet<string> { ".dfy" };
  public override string TargetName => "Dafny";
  public override bool IsStable => true;
  public override bool IsInternal => true;
  public override string TargetExtension => "dfy";
  public override int TargetIndentSize => 4;
  public override bool SupportsInMemoryCompilation => false;
  public override bool TextualTargetIsExecutable => false;

  public override string TargetBasename(string dafnyProgramName) =>
    Regex.Replace(base.TargetBasename(dafnyProgramName), "[^_A-Za-z0-9]", "_");

  public override string TargetBaseDir(string dafnyProgramName) =>
    $"{Path.GetFileNameWithoutExtension(dafnyProgramName)}-dafny/src";

  protected override DafnyWrittenCompiler CreateDafnyWrittenCompiler() {
    return new FDafnyCompiler();
  }

  public FDafnyBackend(DafnyOptions options) : base(options) {
  }
}
