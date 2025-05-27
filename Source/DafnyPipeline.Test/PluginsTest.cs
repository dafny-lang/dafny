using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Reflection;
using System.Threading.Tasks;
using DafnyCore.Test;
using DafnyTestGeneration;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Xunit;
using Microsoft.Dafny;
using Xunit.Abstractions;

namespace DafnyPipeline.Test;

[Collection("Dafny plug-ins tests")]
public class PluginsTest {
  private readonly TextWriter output;

  public PluginsTest(ITestOutputHelper output) {
    this.output = new WriterFromOutputHelper(output);
  }

  /// <summary>
  /// This method creates a library and returns the path to that library.
  /// The library extends a Rewriter so that we can verify that Dafny invokes it if provided in argument.
  /// </summary>
  private string GetLibrary(string name) {
    var assembly = Assembly.GetExecutingAssembly();
    Stream codeStream = assembly.GetManifestResourceStream($"DafnyPipeline.Test._plugins.{name}.cs");
    Assert.NotNull(codeStream);
    string code = new StreamReader(codeStream).ReadToEnd();

    var temp = Path.GetTempFileName();
    var compilation = CSharpCompilation.Create(name);
    var standardLibraries = new List<string>()
    {
      "DafnyCore",
      "System.Runtime",
      "Boogie.Core"
    };
    compilation = compilation.AddReferences(standardLibraries.Select(fileName =>
        MetadataReference.CreateFromFile(Assembly.Load(fileName).Location)))
      .AddReferences(
        MetadataReference.CreateFromFile(typeof(object).GetTypeInfo().Assembly.Location))
      .WithOptions(
        new CSharpCompilationOptions(OutputKind.DynamicallyLinkedLibrary)
      );
    var syntaxTree = CSharpSyntaxTree.ParseText(code);
    compilation = compilation.AddSyntaxTrees(syntaxTree);
    var assemblyPath = $"{temp}.dll";
    var result = compilation.Emit(assemblyPath);

    Assert.True(result.Success, string.Join("\n", result.Diagnostics.Select(d => d.ToString())));
    return assemblyPath;
  }

  [Fact]
  public async Task EnsurePluginIsExecuted() {
    var library = GetLibrary("rewriterPreventingVerificationWithArgument");

    var options = DafnyOptions.CreateUsingOldParser(output);
    options.Plugins.Add(AssemblyPlugin.Load(library, ["because whatever"]));

    var programString = "function test(): int { 1 }";
    var reporter = new BatchErrorReporter(options);
    var dafnyProgram = await Utils.Parse(reporter, programString, false);
    DafnyMain.Resolve(dafnyProgram);

    Assert.Equal(1, reporter.Count(ErrorLevel.Error));
    Assert.Equal("Impossible to continue because whatever", reporter.AllMessagesByLevel[ErrorLevel.Error][0].Message);
  }

  [Fact]
  public async Task EnsurePluginIsExecutedEvenWithoutConfiguration() {
    var library = GetLibrary("rewriterPreventingVerification");

    var options = DafnyOptions.CreateUsingOldParser(output);
    options.Plugins.Add(AssemblyPlugin.Load(library, ["ignored arguments"]));

    var programString = "function test(): int { 1 }";
    var reporter = new BatchErrorReporter(options);
    var dafnyProgram = await Utils.Parse(reporter, programString, false);
    DafnyMain.Resolve(dafnyProgram);
    Assert.Equal(1, reporter.ErrorCount);
    Assert.Equal("Impossible to continue", reporter.AllMessagesByLevel[ErrorLevel.Error][0].Message);
  }

  [Fact]
  public async Task EnsurePluginIsExecutedAndAllowsVerification() {
    var library = GetLibrary("rewriterAllowingVerification");

    var options = DafnyOptions.CreateUsingOldParser(output);
    options.Plugins.Add(AssemblyPlugin.Load(library, ["ignored arguments"]));

    var programString = "function test(): int { 1 }";
    var reporter = new BatchErrorReporter(options);
    var dafnyProgram = await Utils.Parse(reporter, programString, false);
    DafnyMain.Resolve(dafnyProgram);
    Assert.Equal(0, reporter.ErrorCountUntilResolver);
    Assert.Equal(1, reporter.ErrorCount);
  }
}
