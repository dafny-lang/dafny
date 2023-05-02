using System.Collections.Generic;
using System.Collections.ObjectModel;
using System.Diagnostics.Contracts;
using System.IO;
using System.Linq;
using System.Text.RegularExpressions;

namespace Microsoft.Dafny.Compilers;

public class PythonBackend : ExecutableBackend {

  public override IReadOnlySet<string> SupportedExtensions => new HashSet<string> { ".py" };

  public override string TargetName => "Python";
  public override string TargetExtension => "py";
  public override int TargetIndentSize => 4;

  public override string TargetBaseDir(string dafnyProgramName) =>
    $"{Path.GetFileNameWithoutExtension(dafnyProgramName)}-py";

  public override bool SupportsInMemoryCompilation => false;
  public override bool TextualTargetIsExecutable => true;

  public override IReadOnlySet<string> SupportedNativeTypes =>
    new HashSet<string> { "byte", "sbyte", "ushort", "short", "uint", "int", "number", "ulong", "long" };

  protected override SinglePassCompiler CreateCompiler() {
    return new PythonCompiler(Options, Reporter);
  }

  private static readonly Regex ModuleLine = new(@"^\s*assert\s+""([a-zA-Z0-9_]+)""\s*==\s*__name__\s*$");

  private static string FindModuleName(string externFilename) {
    using var rd = new StreamReader(new FileStream(externFilename, FileMode.Open, FileAccess.Read));
    while (rd.ReadLine() is { } line) {
      var match = ModuleLine.Match(line);
      if (match.Success) {
        rd.Close();
        return match.Groups[1].Value;
      }
    }
    rd.Close();
    return externFilename.EndsWith(".py") ? externFilename[..^3] : null;
  }

  bool CopyExternLibraryIntoPlace(string externFilename, string mainProgram, TextWriter outputWriter) {
    // Grossly, we need to look in the file to figure out where to put it
    var moduleName = FindModuleName(externFilename);
    if (moduleName == null) {
      outputWriter.WriteLine($"Unable to determine module name: {externFilename}");
      return false;
    }
    var mainDir = Path.GetDirectoryName(mainProgram);
    Contract.Assert(mainDir != null);
    var tgtFilename = Path.Combine(mainDir, moduleName + ".py");
    var file = new FileInfo(externFilename);
    file.CopyTo(tgtFilename, true);
    if (Options.CompileVerbose) {
      outputWriter.WriteLine($"Additional input {externFilename} copied to {tgtFilename}");
    }
    return true;
  }

  public override void CleanSourceDirectory(string sourceDirectory) {
    var cacheDirectory = Path.Combine(sourceDirectory, "__pycache__");
    try {
      Directory.Delete(cacheDirectory, true);
    } catch (DirectoryNotFoundException) {
    }
  }

  public override bool CompileTargetProgram(string dafnyProgramName, string targetProgramText,
      string /*?*/ callToMain, string /*?*/ targetFilename, ReadOnlyCollection<string> otherFileNames,
      bool runAfterCompile, TextWriter outputWriter, out object compilationResult) {
    compilationResult = null;
    foreach (var otherFileName in otherFileNames) {
      if (Path.GetExtension(otherFileName) != ".py") {
        outputWriter.WriteLine($"Unrecognized file as extra input for Python compilation: {otherFileName}");
        return false;
      }
      if (!CopyExternLibraryIntoPlace(otherFileName, targetFilename, outputWriter)) {
        return false;
      }
    }
    return true;
  }

  public override bool RunTargetProgram(string dafnyProgramName, string targetProgramText, string callToMain, /*?*/
    string targetFilename, ReadOnlyCollection<string> otherFileNames, object compilationResult, TextWriter outputWriter,
    TextWriter errorWriter) {
    Contract.Requires(targetFilename != null || otherFileNames.Count == 0);
    var psi = PrepareProcessStartInfo("python3", Options.MainArgs.Prepend(targetFilename));
    psi.EnvironmentVariables["PYTHONIOENCODING"] = "utf8";
    return 0 == RunProcess(psi, outputWriter, errorWriter);
  }

  public PythonBackend(DafnyOptions options) : base(options) {
  }
}