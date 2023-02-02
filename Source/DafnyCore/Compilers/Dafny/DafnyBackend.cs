using System;
using System.Collections.Generic;
using System.Collections.ObjectModel;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using System.IO;
using System.Linq;
using System.Reflection;
using System.Text;
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

    var where = System.Reflection.Assembly.GetExecutingAssembly().Location;
    where = System.IO.Path.GetDirectoryName(where);
    var dafny = where + "/Dafny.dll";

    var opt = DafnyOptions.O;
    var psi = PrepareProcessStartInfo("dotnet", opt.MainArgs.Prepend("/compileTarget:cs").Prepend("/compile:4").Prepend("/compileVerbose:0").Prepend("/printVerifiedProceduresCount:0").Prepend("/noVerify").Prepend(targetFilename).Prepend(dafny));

    /*
     * When this code was written, the Dafny compiler cannot be made completely silent.
     * This is a problem for this specific compiler and the integration tests because the second
     * call to the compiler makes unexpected writes to the output.
     * The following code is catching the output from the second compiler call (the one that executes the code)
     * and stripping out the first two lines and the last line.
     */

    psi.RedirectStandardOutput = true;
    var process = new Process();
    process.StartInfo = psi;
    var outputBuilder = new List<string>();
    process.OutputDataReceived += (sender, args) => outputBuilder.Add(args.Data);

    try {
      process.Start();
      process.BeginOutputReadLine();
      process.WaitForExit();
      process.CancelOutputRead();

      for (int i = 2; i < outputBuilder.Count - 1; i++) {
        Console.WriteLine(outputBuilder[i]);
      }

      if (process.ExitCode != 0) {
        outputWriter.WriteLine("{0} Process exited with exit code {1}", "", process.ExitCode);
        return false;
      }

    } catch (System.ComponentModel.Win32Exception e) {
      string additionalInfo = $": {e.Message}";
      outputWriter.WriteLine($"Error: Unable to start {psi.FileName}{additionalInfo}");
      return false;
    }

    return true;

  }
}