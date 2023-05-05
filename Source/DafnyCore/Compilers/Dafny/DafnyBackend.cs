using System;
using System.Collections.Generic;
using System.Collections.ObjectModel;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using System.IO;
using System.Linq;

namespace Microsoft.Dafny.Compilers;

public class DafnyBackend : ExecutableBackend {

  public override IReadOnlySet<string> SupportedExtensions => new HashSet<string> { ".dfy" };
  public override string TargetName => "Simple Dafny";
  public override string TargetExtension => "dfy";
  public override int TargetIndentSize => 4;
  public override string TargetBaseDir(string dafnyProgramName) =>
    $"{Path.GetFileNameWithoutExtension(dafnyProgramName)}-dfy";
  public override bool SupportsInMemoryCompilation => false;
  public override bool TextualTargetIsExecutable => false;
  public override bool IsInternal => true;

  protected override SinglePassCompiler CreateCompiler() {
    return new DafnyCompiler(Options, Reporter);
  }

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

  /*
   * The Dafny backend is different from the other backends in that the output code needs to be compiled
   * by the Dafny compiler itself to another backend for execution.
   */
  public override bool RunTargetProgram(string dafnyProgramName, string targetProgramText, string callToMain, /*?*/
    string targetFilename, ReadOnlyCollection<string> otherFileNames, object compilationResult, TextWriter outputWriter,
    TextWriter errorWriter) {
    Contract.Requires(targetFilename != null || otherFileNames.Count == 0);
    
    return RunTargetDafnyProgram(targetFilename, outputWriter);
  }

  public DafnyBackend(DafnyOptions options) : base(options) {
  }
}
