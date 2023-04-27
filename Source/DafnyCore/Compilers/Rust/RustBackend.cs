using System;
using System.Collections.Generic;
using System.Collections.ObjectModel;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using System.IO;
using System.Linq;

namespace Microsoft.Dafny.Compilers;

public class RustBackend : DafnyExecutableBackend {

  public override IReadOnlySet<string> SupportedExtensions => new HashSet<string> { ".rs" };
  public override string TargetLanguage => "Rust";
  public override string TargetExtension => "rs";
  public override int TargetIndentSize => 4;
  public override string TargetBaseDir(string dafnyProgramName) =>
    $"{Path.GetFileNameWithoutExtension(dafnyProgramName)}-rs";
  public override bool SupportsInMemoryCompilation => false;
  public override bool TextualTargetIsExecutable => false;

  protected override DafnyWrittenCompiler CreateDafnyWrittenCompiler() {
    return new RustCompiler();
  }

  public override bool CompileTargetProgram(string dafnyProgramName, string targetProgramText,
      string /*?*/ callToMain, string /*?*/ targetFilename, ReadOnlyCollection<string> otherFileNames,
      bool runAfterCompile, TextWriter outputWriter, out object compilationResult) {
    compilationResult = null;
    return true;
  }
  
  public override bool RunTargetProgram(string dafnyProgramName, string targetProgramText, string /*?*/ callToMain,
    string targetFilename, ReadOnlyCollection<string> otherFileNames, object compilationResult, TextWriter outputWriter) {
    Contract.Requires(targetFilename != null || otherFileNames.Count == 0);


    return true;

  }

  public RustBackend(DafnyOptions options) : base(options) {
  }
}