using System.Collections.Generic;
using System.Collections.ObjectModel;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using System.IO;
using System.Linq;

namespace Microsoft.Dafny.Compilers;

public abstract class ExecutableBackend : Plugins.IExecutableBackend {
  protected SinglePassCompiler compiler;

  protected ExecutableBackend(DafnyOptions options) {
    Options = options;
  }

  public DafnyOptions Options { get; }

  public override IReadOnlySet<Feature> UnsupportedFeatures => CreateCompiler().UnsupportedFeatures;

  public override bool SupportsDatatypeWrapperErasure => CreateCompiler().SupportsDatatypeWrapperErasure;

  public override void Compile(Program dafnyProgram, ConcreteSyntaxTree output) {
    compiler.Compile(dafnyProgram, output);
  }

  public override void OnPreCompile(ErrorReporter reporter, ReadOnlyCollection<string> otherFileNames) {
    base.OnPreCompile(reporter, otherFileNames);
    compiler = CreateCompiler();
  }

  public override void OnPostCompile() {
    base.OnPostCompile();
    compiler.Coverage.WriteLegendFile();
  }

  protected abstract SinglePassCompiler CreateCompiler();

  public override string PublicIdProtect(string name) {
    return compiler.PublicIdProtect(name);
  }

  public override void EmitCallToMain(Method mainMethod, string baseName, ConcreteSyntaxTree callToMainTree) {
    compiler.EmitCallToMain(mainMethod, baseName, callToMainTree);
  }

  public ProcessStartInfo PrepareProcessStartInfo(string programName, IEnumerable<string> args = null) {
    var psi = new ProcessStartInfo(programName) {
      UseShellExecute = false,
      CreateNoWindow = false, // https://github.com/dotnet/runtime/issues/68259
    };
    foreach (var arg in args ?? Enumerable.Empty<string>()) {
      psi.ArgumentList.Add(arg);
    }
    return psi;
  }

  public int RunProcess(ProcessStartInfo psi, TextWriter outputWriter, string errorMessage = null) {
    return StartProcess(psi, outputWriter) is { } process ?
      WaitForExit(process, outputWriter, errorMessage) : -1;
  }

  public int WaitForExit(Process process, TextWriter outputWriter, string errorMessage = null) {
    process.WaitForExit();
    if (process.ExitCode != 0 && errorMessage != null) {
      outputWriter.WriteLine("{0} Process exited with exit code {1}", errorMessage, process.ExitCode);
    }
    return process.ExitCode;
  }

  public Process StartProcess(ProcessStartInfo psi, TextWriter outputWriter) {
    string additionalInfo = "";

    try {
      if (Process.Start(psi) is { } process) {
        return process;
      }
    } catch (System.ComponentModel.Win32Exception e) {
      additionalInfo = $": {e.Message}";
    }

    outputWriter.WriteLine($"Error: Unable to start {psi.FileName}{additionalInfo}");
    return null;
  }

  public override bool CompileTargetProgram(string dafnyProgramName, string targetProgramText, string/*?*/ callToMain, string/*?*/ targetFilename,
    ReadOnlyCollection<string> otherFileNames,
    bool runAfterCompile, TextWriter outputWriter, out object compilationResult) {
    Contract.Requires(dafnyProgramName != null);
    Contract.Requires(targetProgramText != null);
    Contract.Requires(otherFileNames != null);
    Contract.Requires(otherFileNames.Count == 0 || targetFilename != null);
    Contract.Requires(this.SupportsInMemoryCompilation || targetFilename != null);
    Contract.Requires(!runAfterCompile || callToMain != null);
    Contract.Requires(outputWriter != null);

    compilationResult = null;
    return true;
  }

  public override bool RunTargetProgram(string dafnyProgramName, string targetProgramText, string/*?*/ callToMain, string/*?*/ targetFilename, ReadOnlyCollection<string> otherFileNames,
    object compilationResult, TextWriter outputWriter) {
    Contract.Requires(dafnyProgramName != null);
    Contract.Requires(targetProgramText != null);
    Contract.Requires(otherFileNames != null);
    Contract.Requires(otherFileNames.Count == 0 || targetFilename != null);
    Contract.Requires(outputWriter != null);
    return true;
  }

  protected static void WriteFromFile(string inputFilename, TextWriter outputWriter) {
    var rd = new StreamReader(new FileStream(inputFilename, FileMode.Open, FileAccess.Read));
    SinglePassCompiler.WriteFromStream(rd, outputWriter);
  }
}
