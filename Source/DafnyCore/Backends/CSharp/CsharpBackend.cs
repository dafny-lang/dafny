using System;
using System.Collections.Generic;
using System.Collections.ObjectModel;
using System.IO;
using System.Linq;
using System.Reflection;
using System.Text.Json;
using System.Threading.Tasks;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using DafnyCore.Options;

using System;
using System.Collections.Generic;
using System.Collections.ObjectModel;
using System.CommandLine;
using System.Diagnostics.Contracts;
using System.IO;
using System.Linq;
using System.Text.RegularExpressions;
using System.Threading.Tasks;
using DafnyCore.Options;

namespace Microsoft.Dafny.Compilers;

public class CsharpBackend : ExecutableBackend {

  protected override SinglePassCodeGenerator CreateCodeGenerator() {
    return new CsharpCodeGenerator(Options, Reporter);
  }

  public override IReadOnlySet<string> SupportedExtensions => new HashSet<string> { ".cs", ".dll" };

  public override string TargetName => "C#";
  public override bool IsStable => true;
  public override string TargetExtension => "cs";

  public bool NetNamespaceMode { get; set; } = true;
  public string NetNamespace;

  public static readonly Option<string> NetNamespaceCliOption = new("--dotnet-namespace",
    @"This Option is used to specify the .NET namespace for the translated code".TrimStart()) {
  };
  public override IEnumerable<Option<string>> SupportedOptions => new List<Option<string>> { NetNamespaceCliOption };


  // True if the most recently visited AST has a method annotated with {:synthesize}:

  public override string GetCompileName(bool isDefaultModule, string moduleName, string compileName) {
    // var newModuleName = MaybePrependModuleNameWithCodeLocationPrefix(moduleName);
    return isDefaultModule
      ? PublicIdProtect(compileName)
      : base.GetCompileName(isDefaultModule, moduleName, compileName);
  }

  public override bool SupportsInMemoryCompilation => true;
  public override bool TextualTargetIsExecutable => false;

  public override async Task<(bool Success, object CompilationResult)> CompileTargetProgram(string dafnyProgramName,
    string targetProgramText,
    string callToMain /*?*/, string targetFilename /*?*/, ReadOnlyCollection<string> otherFileNames,
    bool runAfterCompile, TextWriter outputWriter) {

    // .NET Core does not allow C# compilation on all platforms using System.CodeDom. You need to use Roslyn libraries. Context: https://github.com/dotnet/runtime/issues/18768
    var compilation = CSharpCompilation.Create(Path.GetFileNameWithoutExtension(dafnyProgramName))
      .WithOptions(new CSharpCompilationOptions(OutputKind.DynamicallyLinkedLibrary))
      .AddReferences(
        MetadataReference.CreateFromFile(typeof(object).GetTypeInfo().Assembly.Location),
        MetadataReference.CreateFromFile(Assembly.Load("mscorlib").Location));

    compilation = compilation.WithOptions(compilation.Options.WithOutputKind(callToMain != null ? OutputKind.ConsoleApplication : OutputKind.DynamicallyLinkedLibrary));

    var tempCompilationResult = new CSharpCompilationResult();
    if (!Options.IncludeRuntime) {
      var libPath = Path.GetDirectoryName(Assembly.GetExecutingAssembly().Location);
      compilation = compilation.AddReferences(MetadataReference.CreateFromFile(Path.Join(libPath, "DafnyRuntime.dll")));
      compilation = compilation.AddReferences(MetadataReference.CreateFromFile(Assembly.Load("netstandard").Location));
    }

    var standardLibraries = new List<string>() {
      "System.Runtime",
      "System.Runtime.Numerics",
      "System.Collections",
      "System.Collections.Immutable",
      "System.Collections.Concurrent",
      "System.Console"
    };
    compilation = compilation.AddReferences(standardLibraries.Select(fileName => MetadataReference.CreateFromFile(Assembly.Load((string)fileName).Location)));

    if (Options.Optimize) {
      compilation = compilation.WithOptions(compilation.Options.WithOptimizationLevel(
        Options.Optimize ? OptimizationLevel.Release : OptimizationLevel.Debug));
    }

    var otherSourceFiles = new List<string>();
    foreach (var file in otherFileNames) {
      string extension = Path.GetExtension(file);
      if (extension != null) { extension = extension.ToLower(); }
      if (extension == ".cs") {
        var normalizedPath = Path.Combine(Path.GetDirectoryName(file), Path.GetFileName(file));
        if (File.Exists(normalizedPath)) {
          otherSourceFiles.Add(normalizedPath);
        } else {
          await outputWriter.WriteLineAsync($"Errors compiling program: Could not find {file}");
          return (false, null);
        }
      } else if (extension == ".dll") {
        compilation = compilation.AddReferences(MetadataReference.CreateFromFile(Path.GetFullPath(file)));
      }
    }

    var source = callToMain == null ? targetProgramText : targetProgramText + callToMain;
    compilation = compilation.AddSyntaxTrees(CSharpSyntaxTree.ParseText(source, null, "source"));
    foreach (var sourceFile in otherSourceFiles) {
      compilation = compilation.AddSyntaxTrees(CSharpSyntaxTree.ParseText(File.ReadAllText(sourceFile), null, sourceFile));
    }
    var outputDir = targetFilename == null ? Directory.GetCurrentDirectory() : Path.GetDirectoryName(Path.GetFullPath(targetFilename));
    Directory.CreateDirectory(outputDir);
    var outputPath = Path.Join(outputDir, Path.GetFileNameWithoutExtension(Path.GetFileName(dafnyProgramName)) + ".dll");
    var outputJson = Path.Join(outputDir, Path.GetFileNameWithoutExtension(Path.GetFileName(dafnyProgramName)) + ".runtimeconfig.json");
    var emitResult = compilation.Emit(outputPath);

    if (emitResult.Success) {
      tempCompilationResult.CompiledAssembly = Assembly.LoadFile(outputPath);
      if (Options.Verbose) {
        await outputWriter.WriteLineAsync($"Compiled assembly into {compilation.AssemblyName}.dll");
      }

      try {
        var configuration = JsonSerializer.Serialize(
          new {
            runtimeOptions = new {
              tfm = "net6.0",
              framework = new {
                name = "Microsoft.NETCore.App",
                version = "6.0.0",
                rollForward = "LatestMinor"
              }
            }
          }, new JsonSerializerOptions() { WriteIndented = true });
        await File.WriteAllTextAsync(outputJson, configuration + Environment.NewLine);
      } catch (Exception e) {
        await outputWriter.WriteLineAsync($"Error trying to write '{outputJson}': {e.Message}");
        return (false, null);
      }
    } else {
      await outputWriter.WriteLineAsync($"Errors compiling program into {compilation.AssemblyName}");
      var errors = emitResult.Diagnostics.Where(d => d.Severity == DiagnosticSeverity.Error).ToList();
      foreach (var ce in errors) {
        await outputWriter.WriteLineAsync(ce.ToString());
        await outputWriter.WriteLineAsync();
      }

      return (false, null);
    }

    return (true, tempCompilationResult);
  }

  private class CSharpCompilationResult {
    public Assembly CompiledAssembly;
  }

  public override async Task<bool> RunTargetProgram(string dafnyProgramName, string targetProgramText, string callToMain,
    string targetFilename /*?*/, ReadOnlyCollection<string> otherFileNames,
    object compilationResult, TextWriter outputWriter, TextWriter errorWriter) {

    var crx = (CSharpCompilationResult)compilationResult;

    foreach (var otherFileName in otherFileNames) {
      if (Path.GetExtension(otherFileName) == ".dll") {
        var targetDirectory = Path.GetDirectoryName(crx.CompiledAssembly.Location);
        File.Copy(otherFileName, Path.Combine(targetDirectory!, Path.GetFileName(otherFileName)), true);
      }
    }

    if (crx.CompiledAssembly == null) {
      throw new Exception("Cannot call run target program on a compilation that failed");
    }
    var psi = PrepareProcessStartInfo("dotnet", new[] { crx.CompiledAssembly.Location }.Concat(Options.MainArgs));
    return await RunProcess(psi, outputWriter, errorWriter) == 0;
  }

  public override void PopulateCoverageReport(CoverageReport coverageReport) {
    codeGenerator.Coverage.PopulateCoverageReport(coverageReport);
  }

  public CsharpBackend(DafnyOptions options) : base(options) {
        try {
TranslationRecord.RegisterLibraryChecks(new Dictionary<Option, OptionCompatibility.OptionCheck> {
      { NetNamespaceCliOption, OptionCompatibility.NoOpOptionCheck }
    });
    } catch ( System.ArgumentException ex) {}
  }
}
