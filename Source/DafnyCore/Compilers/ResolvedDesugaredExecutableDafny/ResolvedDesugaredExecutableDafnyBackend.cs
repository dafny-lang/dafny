using System.Collections.Generic;
using System.CommandLine;
using System.IO;
using System.Text.RegularExpressions;

namespace Microsoft.Dafny.Compilers;

public class ResolvedDesugaredExecutableDafnyBackend : DafnyExecutableBackend {

  public override IReadOnlySet<string> SupportedExtensions => new HashSet<string> { ".dfy" };
  public override string TargetName => "Dafny code as data";
  public override bool IsStable => true;
  public override bool IsInternal => true;
  public override string TargetExtension => "dfy";
  public override string TargetId => "meta";
  public override bool SupportsInMemoryCompilation => false;
  public override bool TextualTargetIsExecutable => false;

  public override string TargetBaseDir(string dafnyProgramName) =>
    $"{Path.GetFileNameWithoutExtension(dafnyProgramName)}-ResolvedDesugaredExecutableDafny/src";

  protected override DafnyWrittenCompiler CreateDafnyWrittenCompiler() {
    return new ResolvedDesugaredExecutableDafnyCompiler();
  }

  public ResolvedDesugaredExecutableDafnyBackend(DafnyOptions options) : base(options) {
  }

  public override Command GetCommand() {
    return new Command(TargetId, $"Translate the resolved Dafny program to equivalent Dafny code that represents the code as data using data type constructors. This representation is useful for metaprogramming tools written in Dafny.");
  }
}
