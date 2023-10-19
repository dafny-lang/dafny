using System;
using System.Collections.Generic;
using System.Collections.ObjectModel;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using System.IO;
using System.Linq;
using System.Runtime.InteropServices;
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

  // private string ComputeExeName(string targetFilename) {
  //   var targetDirectory = Path.GetDirectoryName(Path.GetDirectoryName(targetFilename));
  //   if (RuntimeInformation.IsOSPlatform(OSPlatform.Windows)) {
  //     return Path.Combine(targetDirectory, "target", "debug", Path.GetFileNameWithoutExtension(targetFilename) + ".exe");
  //   } else {
  //     return Path.Combine(targetDirectory, "target", "debug", Path.GetFileNameWithoutExtension(targetFilename));
  //   }
  // }
  //
  // public override bool CompileTargetProgram(string dafnyProgramName, string targetProgramText,
  //     string /*?*/ callToMain, string /*?*/ targetFilename, ReadOnlyCollection<string> otherFileNames,
  //     bool runAfterCompile, TextWriter outputWriter, out object compilationResult) {
  //   compilationResult = null;
  //   return true;
  // }
  //
  // public override bool RunTargetProgram(string dafnyProgramName, string targetProgramText, string /*?*/ callToMain,
  //   string targetFilename, ReadOnlyCollection<string> otherFileNames, object compilationResult, TextWriter outputWriter, TextWriter errorWriter) {
  //   Contract.Requires(targetFilename != null || otherFileNames.Count == 0);
  //   var psi = PrepareProcessStartInfo(ComputeExeName(targetFilename), Options.MainArgs);
  //   return 0 == RunProcess(psi, outputWriter, errorWriter);
  // }

  public FDafnyBackend(DafnyOptions options) : base(options) {
  }
}