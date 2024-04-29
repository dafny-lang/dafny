using System;
using System.Collections.Generic;
using System.Collections.ObjectModel;
using System.IO;
using System.IO.Compression;
using System.Linq;
using System.Threading.Tasks;
using DafnyCore;

namespace Microsoft.Dafny.Compilers;

public class LibraryBackend : ExecutableBackend {
  public LibraryBackend(DafnyOptions options) : base(options) {
  }

  public override IReadOnlySet<string> SupportedExtensions => new HashSet<string> { };

  public override string TargetName => "Dafny Library (.doo)";
  public override bool IsStable => false;

  public override string TargetExtension => "doo";
  public override string TargetId => "lib";

  public override string TargetBaseDir(string dafnyProgramName) =>
    $"{Path.GetFileNameWithoutExtension(dafnyProgramName)}-lib";

  public override bool TextualTargetIsExecutable => false;

  public override bool SupportsInMemoryCompilation => false;

  public override IReadOnlySet<Feature> UnsupportedFeatures => new HashSet<Feature> {
    Feature.LegacyCLI,
    Feature.RuntimeCoverageReport
  };

  // Necessary since Compiler is null
  public override string ModuleSeparator => ".";

  /// <summary>
  /// Serializing the state of the Program passed to this backend,
  /// after resolution, can be problematic.
  /// If nothing else, very early on in the resolution process
  /// we create explicit module definitions for implicit ones appearing
  /// in qualified names such as `module A.B.C { ... }`,
  /// and this means that multiple .doo files would then not be able to
  /// share these prefixes without hitting duplicate name errors.
  ///
  /// Instead we serialize the state of the program immediately after parsing.
  /// See also ProgramParser.ParseFiles().
  /// 
  /// This could be captured somewhere else, such as on the Program itself,
  /// if having this state here hampers reuse in the future,
  /// especially parallel processing.
  /// </summary>
  internal Program ProgramAfterParsing { get; set; }

  protected override SinglePassCodeGenerator CreateCodeGenerator() {
    return null;
  }

  public override Task<bool> OnPostGenerate(string dafnyProgramName, string targetFilename, TextWriter outputWriter) {
    // Not calling base.OnPostCompile() since it references `compiler`
    return Task.FromResult(true);
  }

  public override string PublicIdProtect(string name) {
    throw new NotSupportedException();
  }

  public override void Compile(Program dafnyProgram, ConcreteSyntaxTree output) {
    if (!Options.UsingNewCli) {
      throw new UnsupportedFeatureException(dafnyProgram.GetStartOfFirstFileToken(), Feature.LegacyCLI);
    }

    var dooFile = new DooFile(ProgramAfterParsing);
    dooFile.Write(output);
  }

  public override void EmitCallToMain(Method mainMethod, string baseName, ConcreteSyntaxTree callToMainTree) {
    // No-op
  }

  private string DooFilePath(string dafnyProgramName) {
    return Path.GetFullPath(Path.ChangeExtension(dafnyProgramName, ".doo"));
  }

  public override Task<(bool Success, object CompilationResult)> CompileTargetProgram(string dafnyProgramName,
    string targetProgramText, string callToMain,
    string targetFilename,
    ReadOnlyCollection<string> otherFileNames, bool runAfterCompile, TextWriter outputWriter) {

    var targetDirectory = Path.GetFullPath(Path.GetDirectoryName(targetFilename));
    var dooPath = DooFilePath(dafnyProgramName);

    File.Delete(dooPath);
    ZipFile.CreateFromDirectory(targetDirectory, dooPath);

    return Task.FromResult((true, (object)null));
  }

  public override Task<bool> RunTargetProgram(string dafnyProgramName, string targetProgramText, string callToMain,
    string targetFilename,
    ReadOnlyCollection<string> otherFileNames, object compilationResult, TextWriter outputWriter,
    TextWriter errorWriter) {
    var dooPath = DooFilePath(dafnyProgramName);
    return RunTargetDafnyProgram(dooPath, outputWriter, errorWriter, true);
  }
}