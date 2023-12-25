using System.Collections.Generic;
using System.Collections.ObjectModel;
using System.IO;
using Dafny;
using D2DInterpreter;

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

  public override bool RunTargetProgram(string dafnyProgramName, string targetProgramText, string /*?*/ callToMain,
    string targetFilename, ReadOnlyCollection<string> otherFileNames, object compilationResult, TextWriter outputWriter, TextWriter errorWriter) {
    Sequence<DAST.Module> program = ((ResolvedDesugaredExecutableDafnyCompiler)dafnyCompiler).Program;
    Interpreter.Run(program);
    return true;
  }
  
  public ResolvedDesugaredExecutableDafnyBackend(DafnyOptions options) : base(options) {
  }
}
