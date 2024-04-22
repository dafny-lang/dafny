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

    var disallowedAssumptions = dafnyProgram.Assumptions(null)
      .Where(a => !a.desc.allowedInLibraries);
    foreach (var assumption in disallowedAssumptions) {
      var message = assumption.desc.issue.Replace("{", "{{").Replace("}", "}}");
      Reporter.Error(MessageSource.Compiler, assumption.tok, message, message);
    }

    var dooFile = new DooFile(dafnyProgram.AfterParsingClone);
    dooFile.Write(output);
  }

  public override void EmitCallToMain(Method mainMethod, string baseName, ConcreteSyntaxTree callToMainTree) {
    // No-op
  }

  private string DooFilePath(string dafnyProgramName) {
    return Path.GetFullPath(Path.ChangeExtension(dafnyProgramName, DooFile.Extension));
  }

  public override async Task<(bool Success, object CompilationResult)> CompileTargetProgram(string dafnyProgramName,
    string targetProgramText, string callToMain,
    string targetFilename,
    ReadOnlyCollection<string> otherFileNames, bool runAfterCompile, TextWriter outputWriter) {

    var targetDirectory = Path.GetFullPath(Path.GetDirectoryName(targetFilename));
    var dooPath = DooFilePath(dafnyProgramName);

    File.Delete(dooPath);
    ZipFile.CreateFromDirectory(targetDirectory, dooPath);
    if (Options.Verbose) {
      await outputWriter.WriteLineAsync($"Wrote Dafny library to {dooPath}");
    }

    return (true, null);
  }

  public override Task<bool> RunTargetProgram(string dafnyProgramName, string targetProgramText, string callToMain,
    string targetFilename,
    ReadOnlyCollection<string> otherFileNames, object compilationResult, TextWriter outputWriter,
    TextWriter errorWriter) {
    var dooPath = DooFilePath(dafnyProgramName);
    return RunTargetDafnyProgram(dooPath, outputWriter, errorWriter, true);
  }
}