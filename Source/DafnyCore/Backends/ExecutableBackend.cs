using System;
using System.Collections.Generic;
using System.Collections.ObjectModel;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using System.IO;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using DafnyCore.Options;
using Microsoft.Dafny.Compilers;
using Microsoft.Dafny.Plugins;

namespace Microsoft.Dafny;

public abstract class ExecutableBackend : IExecutableBackend {
  // May be null for backends that don't use the single-pass compiler logic
  protected SinglePassCodeGenerator codeGenerator;

  protected ExecutableBackend(DafnyOptions options) : base(options) {
  }

  public override IReadOnlySet<Feature> UnsupportedFeatures => CreateCodeGenerator().UnsupportedFeatures;

  public override bool SupportsDatatypeWrapperErasure =>
    CreateCodeGenerator()?.SupportsDatatypeWrapperErasure ?? base.SupportsDatatypeWrapperErasure;

  public override string ModuleSeparator => CodeGenerator.ModuleSeparator;

  public override void Compile(Program dafnyProgram, string dafnyProgramName, ConcreteSyntaxTree output) {
    ProcessTranslationRecords(dafnyProgram, dafnyProgramName, output);
    CheckInstantiationReplaceableModules(dafnyProgram);
    ProcessOuterModules(dafnyProgram);

    CodeGenerator.Compile(dafnyProgram, output);
  }

  protected void ProcessTranslationRecords(Program dafnyProgram, string dafnyProgramName, ConcreteSyntaxTree output) {
    // Process --translation-record options, since translation may need that data to translate correctly.
    dafnyProgram.Compilation.AlreadyTranslatedRecord = TranslationRecord.Empty(dafnyProgram);
    var records = dafnyProgram.Options.Get(TranslationRecords);
    if (records != null) {
      foreach (var path in records) {
        TranslationRecord.ReadValidateAndMerge(dafnyProgram, path.FullName, Token.Cli);
      }
    }

    // Write out the translation record for THIS translation before compiling,
    // in case the compilation process mutates the program.
    var translationRecord = new TranslationRecord(dafnyProgram);
    var baseName = Path.GetFileNameWithoutExtension(dafnyProgramName);
    var dtrFilePath = dafnyProgram.Options.Get(TranslationRecordOutput)?.FullName ?? $"{baseName}-{TargetId}.dtr";
    var dtrWriter = output.NewFile(dtrFilePath);
    translationRecord.Write(dtrWriter);
  }

  protected void CheckInstantiationReplaceableModules(Program dafnyProgram) {
    foreach (var compiledModule in dafnyProgram.Modules()) {
      if (compiledModule.Implements is { Kind: ImplementationKind.Replacement }) {
        if (compiledModule.IsExtern(Options, out _, out var name) && name != null) {
          Reporter!.Error(MessageSource.Compiler, compiledModule.Origin,
            "inside a module that replaces another, {:extern} attributes may only be used without arguments");
        }
      }

      if (compiledModule.ModuleKind == ModuleKindEnum.Replaceable && dafnyProgram.Replacements.GetValueOrDefault(compiledModule) == null) {
        if (compiledModule.ShouldCompile(dafnyProgram.Compilation)) {
          Reporter!.Error(MessageSource.Compiler, compiledModule.Origin,
            $"when producing executable code, replaceable modules must be replaced somewhere in the program. For example, `module {compiledModule.Name}Impl replaces {compiledModule.Name} {{ ... }}`");
        }
      }
    }
  }

  protected void ProcessOuterModules(Program dafnyProgram) {
    // Apply the --outer-module option from any translation records for libraries,
    // but only to top-level modules.
    var outerModules = new Dictionary<string, ModuleDefinition>();
    foreach (var module in dafnyProgram.CompileModules) {
      if (module.EnclosingModule is not DefaultModuleDefinition) {
        continue;
      }

      var recordedOuterModuleName = (string)dafnyProgram.Compilation.AlreadyTranslatedRecord.Get(null, module.FullDafnyName, OuterModule);
      if (recordedOuterModuleName == null) {
        continue;
      }

      var outerModule = outerModules.GetOrCreate(recordedOuterModuleName, () => CreateOuterModule(recordedOuterModuleName));
      module.EnclosingModule = outerModule;
    }

    // Apply the local --output-module option if there is one
    var outerModuleName = Options.Get(OuterModule);
    if (outerModuleName != null) {
      var rootUserModule = outerModules.GetOrCreate(outerModuleName, () => CreateOuterModule(outerModuleName));
      dafnyProgram.DefaultModuleDef.NameNode = rootUserModule.NameNode;
      dafnyProgram.DefaultModuleDef.EnclosingModule = rootUserModule.EnclosingModule;
    }

    foreach (var module in dafnyProgram.CompileModules) {
      module.ClearNameCache();
    }
  }

  private static ModuleDefinition CreateOuterModule(string moduleName) {
    var outerModules = moduleName.Split(".");

    ModuleDefinition module = null;
    foreach (var outerModule in outerModules) {
      var thisModule = new ModuleDefinition(SourceOrigin.NoToken, new Name(outerModule), [],
        ModuleKindEnum.Concrete, false,
        null, null, null) {
        EnclosingModule = module
      };
      module = thisModule;
    }

    return module;
  }

  public override void OnPreCompile(ErrorReporter reporter, ReadOnlyCollection<string> otherFileNames) {
    base.OnPreCompile(reporter, otherFileNames);
    codeGenerator = CreateCodeGenerator();
  }

  SinglePassCodeGenerator CodeGenerator {
    get {
      if (codeGenerator == null) {
        codeGenerator = CreateCodeGenerator();
      }

      return codeGenerator;
    }
  }

  public override Task<bool> OnPostGenerate(string dafnyProgramName, string targetDirectory, TextWriter outputWriter) {
    CodeGenerator.Coverage.WriteLegendFile();
    return Task.FromResult(true);
  }

  protected abstract SinglePassCodeGenerator CreateCodeGenerator();

  public override string PublicIdProtect(string name) {
    return CodeGenerator.PublicIdProtect(name);
  }

  public override void EmitCallToMain(Method mainMethod, string baseName, ConcreteSyntaxTree callToMainTree) {
    CodeGenerator.EmitCallToMain(mainMethod, baseName, callToMainTree);
  }

  public ProcessStartInfo PrepareProcessStartInfo(string programName, IEnumerable<string> args = null) {
    var psi = new ProcessStartInfo(programName) {
      UseShellExecute = false,
      CreateNoWindow = false, // https://github.com/dotnet/runtime/issues/68259
      RedirectStandardOutput = true,
    };
    foreach (var arg in args ?? []) {
      psi.ArgumentList.Add(arg);
    }
    return psi;
  }

  public Task<int> RunProcess(ProcessStartInfo psi,
    TextWriter outputWriter,
    TextWriter errorWriter,
    string errorMessage = null) {
    if (OutputWriterEncoding != null) {
      psi.StandardOutputEncoding = OutputWriterEncoding;
    }

    return StartProcess(psi, outputWriter) is { } process ?
      WaitForExit(process, outputWriter, errorWriter, errorMessage) : Task.FromResult(-1);
  }

  public virtual Encoding OutputWriterEncoding => null;

  public async Task<int> WaitForExit(Process process, TextWriter outputWriter, TextWriter errorWriter, string errorMessage = null) {

    var errorTask = PassthroughBuffer(process.StandardError, errorWriter);
    var outputTask = PassthroughBuffer(process.StandardOutput, outputWriter);
    await process.WaitForExitAsync();
    await errorTask;
    await outputTask;
    if (process.ExitCode != 0 && errorMessage != null) {
      await outputWriter.WriteLineAsync($"{errorMessage} Process exited with exit code {process.ExitCode}");
    }

    return process.ExitCode;
  }


  protected static async Task PassthroughBuffer(TextReader input, TextWriter output) {
    char[] buffer = new char[256];
    int readCount;
    while ((readCount = await input.ReadBlockAsync(buffer)) > 0) {
      await output.WriteAsync(buffer, 0, readCount);
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

  public override Task<(bool Success, object CompilationResult)> CompileTargetProgram(string dafnyProgramName,
    string targetProgramText,
    string callToMain /*?*/, string targetFilename, /*?*/
    ReadOnlyCollection<string> otherFileNames,
    bool runAfterCompile, TextWriter outputWriter) {
    Contract.Requires(dafnyProgramName != null);
    Contract.Requires(targetProgramText != null);
    Contract.Requires(otherFileNames != null);
    Contract.Requires(otherFileNames.Count == 0 || targetFilename != null);
    Contract.Requires(this.SupportsInMemoryCompilation || targetFilename != null);
    Contract.Requires(!runAfterCompile || callToMain != null);
    Contract.Requires(outputWriter != null);

    return Task.FromResult((true, (object)null));
  }

  public override Task<bool> RunTargetProgram(string dafnyProgramName, string targetProgramText,
    string callToMain, /*?*/
    string targetFilename /*?*/, ReadOnlyCollection<string> otherFileNames,
    object compilationResult, TextWriter outputWriter, TextWriter errorWriter) {
    Contract.Requires(dafnyProgramName != null);
    Contract.Requires(targetProgramText != null);
    Contract.Requires(otherFileNames != null);
    Contract.Requires(otherFileNames.Count == 0 || targetFilename != null);
    Contract.Requires(outputWriter != null);
    return Task.FromResult(true);
  }

  public override void InstrumentCompiler(CompilerInstrumenter instrumenter, Program dafnyProgram) {
    if (CodeGenerator == null) {
      return;
    }

    instrumenter.Instrument(this, CodeGenerator, dafnyProgram);
  }

  protected static void WriteFromFile(string inputFilename, TextWriter outputWriter) {
    var rd = new StreamReader(new FileStream(inputFilename, FileMode.Open, FileAccess.Read));
    SinglePassCodeGenerator.WriteFromStream(rd, outputWriter);
  }

  protected async Task<bool> RunTargetDafnyProgram(string targetFilename, TextWriter outputWriter, TextWriter errorWriter, bool verify) {

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
    await Console.Out.WriteLineAsync(string.Join(", ", psi.ArgumentList));
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
      await process.WaitForExitAsync();
      process.CancelOutputRead();
      process.CancelErrorRead();

      for (int i = 2; i < outputBuilder.Count - 1; i++) {
        await outputWriter.WriteLineAsync(outputBuilder[i]);
      }

      for (int i = 0; i < errorBuilder.Count - 1; i++) {
        await errorWriter.WriteLineAsync(errorBuilder[i]);
      }

      if (process.ExitCode != 0) {
        await outputWriter.WriteLineAsync($"Process exited with exit code {process.ExitCode}");
        return false;
      }

    } catch (System.ComponentModel.Win32Exception e) {
      string additionalInfo = $": {e.Message}";
      await outputWriter.WriteLineAsync($"Error: Unable to start {psi.FileName}{additionalInfo}");
      return false;
    }

    return true;
  }
}
