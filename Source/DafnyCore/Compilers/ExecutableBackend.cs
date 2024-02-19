using System;
using System.Collections.Generic;
using System.Collections.ObjectModel;
using System.CommandLine;
using System.Data.SqlTypes;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using System.IO;
using System.Linq;
using System.Runtime.InteropServices;
using System.Text;
using System.Threading.Tasks;
using Microsoft.Dafny.Plugins;
using Microsoft.Win32;

namespace Microsoft.Dafny.Compilers;

public abstract class ExecutableBackend : IExecutableBackend {
  // May be null for backends that don't use the single-pass compiler logic
  protected SinglePassCompiler compiler;

  protected ExecutableBackend(DafnyOptions options) : base(options) {
  }

  public override IReadOnlySet<Feature> UnsupportedFeatures => CreateCompiler().UnsupportedFeatures;

  public override bool SupportsDatatypeWrapperErasure =>
    CreateCompiler()?.SupportsDatatypeWrapperErasure ?? base.SupportsDatatypeWrapperErasure;

  public override string ModuleSeparator => Compiler.ModuleSeparator;

  public override void Compile(Program dafnyProgram, ConcreteSyntaxTree output) {
    CheckInstantiationReplaceableModules(dafnyProgram);
    ProcessOuterModules(dafnyProgram);
    Compiler.Compile(dafnyProgram, output);
  }

  protected void CheckInstantiationReplaceableModules(Program dafnyProgram) {
    foreach (var compiledModule in dafnyProgram.Modules()) {
      if (compiledModule.Implements is { Kind: ImplementationKind.Replacement }) {
        if (compiledModule.IsExtern(Options, out _, out var name) && name != null) {
          Reporter!.Error(MessageSource.Compiler, compiledModule.Tok,
            "inside a module that replaces another, {:extern} attributes may only be used without arguments");
        }
      }

      if (compiledModule.ModuleKind == ModuleKindEnum.Replaceable && compiledModule.Replacement == null) {
        if (compiledModule.ShouldCompile(dafnyProgram.Compilation)) {
          Reporter!.Error(MessageSource.Compiler, compiledModule.Tok,
            $"when producing executable code, replaceable modules must be replaced somewhere in the program. For example, `module {compiledModule.Name}Impl replaces {compiledModule.Name} {{ ... }}`");
        }
      }
    }
  }

  protected void ProcessOuterModules(Program dafnyProgram) {
    var outerModules = GetOuterModules();
    ModuleDefinition rootUserModule = null;
    foreach (var outerModule in outerModules) {
      var newRoot = new ModuleDefinition(RangeToken.NoToken, new Name(outerModule), new List<IToken>(),
        ModuleKindEnum.Concrete, false,
        null, null, null);
      newRoot.EnclosingModule = rootUserModule;
      rootUserModule = newRoot;
    }

    if (rootUserModule != null) {
      dafnyProgram.DefaultModuleDef.NameNode = rootUserModule.NameNode;
      dafnyProgram.DefaultModuleDef.EnclosingModule = rootUserModule.EnclosingModule;
    }

    foreach (var module in dafnyProgram.CompileModules) {
      module.ClearNameCache();
    }
  }

  public override void OnPreCompile(ErrorReporter reporter, ReadOnlyCollection<string> otherFileNames) {
    base.OnPreCompile(reporter, otherFileNames);
    compiler = CreateCompiler();
  }

  SinglePassCompiler Compiler {
    get {
      if (compiler == null) {
        compiler = CreateCompiler();
      }

      return compiler;
    }
  }

  public override bool OnPostGenerate(string dafnyProgramName, string targetDirectory, TextWriter outputWriter) {
    Compiler.Coverage.WriteLegendFile();
    return true;
  }

  protected abstract SinglePassCompiler CreateCompiler();

  public override string PublicIdProtect(string name) {
    return Compiler.PublicIdProtect(name);
  }

  public override void EmitCallToMain(Method mainMethod, string baseName, ConcreteSyntaxTree callToMainTree) {
    Compiler.EmitCallToMain(mainMethod, baseName, callToMainTree);
  }

  public ProcessStartInfo PrepareProcessStartInfo(string programName, IEnumerable<string> args = null) {
    var psi = new ProcessStartInfo(programName) {
      UseShellExecute = false,
      CreateNoWindow = false, // https://github.com/dotnet/runtime/issues/68259
      RedirectStandardOutput = true,
    };
    foreach (var arg in args ?? Enumerable.Empty<string>()) {
      psi.ArgumentList.Add(arg);
    }
    return psi;
  }

  public int RunProcess(ProcessStartInfo psi,
    TextWriter outputWriter,
    TextWriter errorWriter,
    string errorMessage = null) {
    return StartProcess(psi, outputWriter) is { } process ?
      WaitForExit(process, outputWriter, errorWriter, errorMessage) : -1;
  }

  public int WaitForExit(Process process, TextWriter outputWriter, TextWriter errorWriter, string errorMessage = null) {

    var errorProcessing = Task.Run(() => {
      PassthroughBuffer(process.StandardError, errorWriter);
    });
    PassthroughBuffer(process.StandardOutput, outputWriter);
    process.WaitForExit();
    if (process.ExitCode != 0 && errorMessage != null) {
      outputWriter.WriteLine("{0} Process exited with exit code {1}", errorMessage, process.ExitCode);
    }

#pragma warning disable VSTHRD002
    errorProcessing.Wait();
#pragma warning restore VSTHRD002
    return process.ExitCode;
  }


  // We read character by character because we did not find a way to ensure
  // final newlines are kept when reading line by line
  protected static void PassthroughBuffer(TextReader input, TextWriter output) {
    int current;
    while ((current = input.Read()) != -1) {
      output.Write((char)current);
    }
  }

  public Process StartProcess(ProcessStartInfo psi, TextWriter outputWriter) {
    string additionalInfo = "";

    try {
      psi.RedirectStandardError = true;
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

  public override bool RunTargetProgram(string dafnyProgramName, string targetProgramText, string callToMain /*?*/,
    string targetFilename /*?*/, ReadOnlyCollection<string> otherFileNames,
    object compilationResult, TextWriter outputWriter, TextWriter errorWriter) {
    Contract.Requires(dafnyProgramName != null);
    Contract.Requires(targetProgramText != null);
    Contract.Requires(otherFileNames != null);
    Contract.Requires(otherFileNames.Count == 0 || targetFilename != null);
    Contract.Requires(outputWriter != null);
    return true;
  }

  public override void InstrumentCompiler(CompilerInstrumenter instrumenter, Program dafnyProgram) {
    if (Compiler == null) {
      return;
    }

    instrumenter.Instrument(this, Compiler, dafnyProgram);
  }

  protected static void WriteFromFile(string inputFilename, TextWriter outputWriter) {
    var rd = new StreamReader(new FileStream(inputFilename, FileMode.Open, FileAccess.Read));
    SinglePassCompiler.WriteFromStream(rd, outputWriter);
  }

  protected bool RunTargetDafnyProgram(string targetFilename, TextWriter outputWriter, TextWriter errorWriter, bool verify) {

    /*
     * In order to work for the continuous integration, we need to call the Dafny compiler using dotnet
     * because dafny is not currently in the path
     */

    var where = System.Reflection.Assembly.GetExecutingAssembly().Location;
    where = Path.GetDirectoryName(where);
    var dafny = where + "/Dafny.dll";

    var opt = Options;
    var args = opt.MainArgs
      .Prepend(targetFilename);
    if (!verify) {
      args = args.Prepend("--no-verify");
    }
    args = args
      .Prepend("--target:cs")
      .Prepend("run")
      .Prepend(dafny);
    var psi = PrepareProcessStartInfo("dotnet", args);
    Console.Out.WriteLine(string.Join(", ", psi.ArgumentList));
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
    var errorBuilder = new List<string>();
    process.OutputDataReceived += (sender, args) => outputBuilder.Add(args.Data);
    process.ErrorDataReceived += (sender, args) => errorBuilder.Add(args.Data);

    try {
      process.Start();
      process.BeginOutputReadLine();
      process.BeginErrorReadLine();
      process.WaitForExit();
      process.CancelOutputRead();
      process.CancelErrorRead();

      for (int i = 2; i < outputBuilder.Count - 1; i++) {
        outputWriter.WriteLine(outputBuilder[i]);
      }

      for (int i = 0; i < errorBuilder.Count - 1; i++) {
        errorWriter.WriteLine(errorBuilder[i]);
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
