using System;
using System.Collections.Generic;
using System.Collections.ObjectModel;
using System.IO;
using System.Linq;
using System.Reflection;
using System.Runtime.Loader;
using System.Text.Json;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;

namespace Microsoft.Dafny.Compilers;

public class CsharpBackend : ExecutableBackend {
  protected override SinglePassCompiler CreateCompiler() {
    return new CsharpCompiler(Options, Reporter);
  }

  public override IReadOnlySet<string> SupportedExtensions => new HashSet<string> { ".cs", ".dll" };

  public override string TargetLanguage => "C#";
  public override string TargetExtension => "cs";

  // True if the most recently visited AST has a method annotated with {:synthesize}:

  public override string GetCompileName(bool isDefaultModule, string moduleName, string compileName) {
    return isDefaultModule
      ? PublicIdProtect(compileName)
      : base.GetCompileName(isDefaultModule, moduleName, compileName);
  }

  public override bool SupportsInMemoryCompilation => true;
  public override bool TextualTargetIsExecutable => false;

  public override bool CompileTargetProgram(string dafnyProgramName, string targetProgramText, string/*?*/ callToMain, string/*?*/ targetFilename, ReadOnlyCollection<string> otherFileNames,
    bool runAfterCompile, TextWriter outputWriter, out object compilationResult) {

    compilationResult = null;

    // .NET Core does not allow C# compilation on all platforms using System.CodeDom. You need to use Roslyn libraries. Context: https://github.com/dotnet/runtime/issues/18768
    var compilation = CSharpCompilation.Create(Path.GetFileNameWithoutExtension(dafnyProgramName))
      .WithOptions(new CSharpCompilationOptions(OutputKind.DynamicallyLinkedLibrary))
      .AddReferences(
        MetadataReference.CreateFromFile(typeof(object).GetTypeInfo().Assembly.Location),
        MetadataReference.CreateFromFile(Assembly.Load("mscorlib").Location));

    var inMemory = false;
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
          outputWriter.WriteLine("Errors compiling program: Could not find {0}", file);
          return false;
        }
      } else if (extension == ".dll") {
        compilation = compilation.AddReferences(MetadataReference.CreateFromFile(Path.GetFullPath(file)));
      }
    }

    var source = callToMain == null ? targetProgramText : targetProgramText + callToMain;
    compilation = compilation.AddSyntaxTrees(CSharpSyntaxTree.ParseText(source));
    foreach (var sourceFile in otherSourceFiles) {
      compilation = compilation.AddSyntaxTrees(CSharpSyntaxTree.ParseText(File.ReadAllText(sourceFile)));
    }
    var outputDir = targetFilename == null ? Directory.GetCurrentDirectory() : Path.GetDirectoryName(Path.GetFullPath(targetFilename));
    var outputPath = Path.Join(outputDir, Path.GetFileNameWithoutExtension(Path.GetFileName(dafnyProgramName)) + ".dll");
    var outputJson = Path.Join(outputDir, Path.GetFileNameWithoutExtension(Path.GetFileName(dafnyProgramName)) + ".runtimeconfig.json");
    var emitResult = compilation.Emit(outputPath);

    if (emitResult.Success) {
      tempCompilationResult.CompiledAssembly = Assembly.LoadFile(outputPath);
      if (Options.CompileVerbose) {
        outputWriter.WriteLine("Compiled assembly into {0}.dll", compilation.AssemblyName);
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
          }, new JsonSerializerOptions() {WriteIndented = true});
        File.WriteAllText(outputJson, configuration + Environment.NewLine);
      } catch (Exception e) {
        outputWriter.WriteLine($"Error trying to write '{outputJson}': {e.Message}");
        return false;
      }
    } else {
      outputWriter.WriteLine("Errors compiling program into {0}", compilation.AssemblyName);
      var errors = emitResult.Diagnostics.Where(d => d.Severity == DiagnosticSeverity.Error).ToList();
      foreach (var ce in errors) {
        outputWriter.WriteLine(ce.ToString());
        outputWriter.WriteLine();
      }

      return false;
    }

    compilationResult = tempCompilationResult;
    return true;
  }

  private class CSharpCompilationResult {
    public Assembly CompiledAssembly;
  }

  public override bool RunTargetProgram(string dafnyProgramName, string targetProgramText, string callToMain, string/*?*/ targetFilename, ReadOnlyCollection<string> otherFileNames,
    object compilationResult, TextWriter outputWriter) {

    var crx = (CSharpCompilationResult)compilationResult;

    foreach (var otherFileName in otherFileNames) {
      if (Path.GetExtension(otherFileName) == ".dll") {
        AssemblyLoadContext.Default.LoadFromAssemblyPath(Path.GetFullPath(otherFileName));
      }
    }

    if (crx.CompiledAssembly == null) {
      throw new Exception("Cannot call run target program on a compilation that failed");
    }

    var psi = PrepareProcessStartInfo("dotnet", new[] { crx.CompiledAssembly.Location }.Concat(Options.MainArgs));
    return RunProcess(psi, outputWriter) == 0;
  }

  public CsharpBackend(DafnyOptions options) : base(options) {
  }
}
