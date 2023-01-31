using System.Collections.Generic;
using System.Collections.ObjectModel;
using System.Diagnostics.Contracts;
using System.IO;
using System.Linq;
using System.Text.RegularExpressions;

namespace Microsoft.Dafny.Compilers;

public class DafnyBackend : ExecutableBackend {

  public override IReadOnlySet<string> SupportedExtensions => new HashSet<string> { ".dfy" };

  public override string TargetLanguage => "Dafny";
  public override string TargetExtension => "dfy";
  public override int TargetIndentSize => 4;

  public override string TargetBaseDir(string dafnyProgramName) =>
    $"{Path.GetFileNameWithoutExtension(dafnyProgramName)}-dfy";

  public override bool SupportsInMemoryCompilation => false;
  public override bool TextualTargetIsExecutable => false;

  public override IReadOnlySet<string> SupportedNativeTypes =>
    new HashSet<string> { "byte", "sbyte", "ushort", "short", "uint", "int", "number", "ulong", "long" };

  protected override SinglePassCompiler CreateCompiler() {
    return new DafnyCompiler(Reporter);
  }

  private static readonly Regex ModuleLine = new(@"^\s*assert\s+""([a-zA-Z0-9_]+)""\s*==\s*__name__\s*$");

  public override bool CompileTargetProgram(string dafnyProgramName, string targetProgramText,
      string /*?*/ callToMain, string /*?*/ targetFilename, ReadOnlyCollection<string> otherFileNames,
      bool runAfterCompile, TextWriter outputWriter, out object compilationResult) {
    compilationResult = null;
    foreach (var otherFileName in otherFileNames) {
      if (Path.GetExtension(otherFileName) != ".dfy") {
        outputWriter.WriteLine($"Unrecognized file as extra input for Dafny compilation: {otherFileName}");
        return false;
      }
    }
    return true;
  }

  public override bool RunTargetProgram(string dafnyProgramName, string targetProgramText, string /*?*/ callToMain,
    string targetFilename, ReadOnlyCollection<string> otherFileNames, object compilationResult, TextWriter outputWriter) {
    Contract.Requires(targetFilename != null || otherFileNames.Count == 0);
    var opt = DafnyOptions.O;
    var psi = PrepareProcessStartInfo("dafny", opt.MainArgs.Prepend("/compileTarget:cs").Prepend("/compile:3").Prepend(targetFilename));
    return 0 == RunProcess(psi, outputWriter);
  }
}