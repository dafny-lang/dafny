using System.Collections.Generic;
using System.Collections.ObjectModel;
using System.IO;
using System.IO.Compression;
using DafnyCore;

namespace Microsoft.Dafny.Compilers.Doo; 

public class DooBackend : ExecutableBackend {
  public DooBackend(DafnyOptions options) : base(options)
  {
  }

  public override IReadOnlySet<string> SupportedExtensions => new HashSet<string> {};

  public override string TargetLanguage => "Doo";

  public override string TargetExtension => "doo";
  
  public override string TargetBaseDir(string dafnyProgramName) =>
    $"{Path.GetFileNameWithoutExtension(dafnyProgramName)}-doo";

  public override bool TextualTargetIsExecutable => false;

  public override bool SupportsInMemoryCompilation => false;
  
  protected override SinglePassCompiler CreateCompiler() {
    return new DooCompiler(Options, Reporter);
  }
  
  public override void Compile(Program dafnyProgram, ConcreteSyntaxTree output) {
    var dooFile = new DooFile(dafnyProgram);
    dooFile.Write(output);
  }

  public override bool CompileTargetProgram(string dafnyProgramName, string targetProgramText, string callToMain, string targetFilename,
    ReadOnlyCollection<string> otherFileNames, bool runAfterCompile, TextWriter outputWriter, out object compilationResult) {
    
    var targetDirectory = Path.GetFullPath(Path.GetDirectoryName(targetFilename));
    var dooPath = Path.GetFullPath(Path.ChangeExtension(dafnyProgramName, ".doo"));
    ZipFile.CreateFromDirectory(targetDirectory, dooPath);

    compilationResult = null;
    return true;
  }
}