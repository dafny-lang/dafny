using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Reflection;
using System.Text.Json;
using System.Threading.Tasks;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Xunit;
using Microsoft.Dafny;

namespace DafnyPipeline.Test;

[Collection("Dafny plug-ins tests")]
public class PluginsTest {
  /// <summary>
  /// This method creates a library and returns the path to that library.
  /// The library extends a Rewriter so that we can verify that Dafny invokes it if provided in argument.
  /// </summary>
  public async Task<string> GetLibrary(string code) {
    var temp = Path.GetTempFileName();
    var compilation = CSharpCompilation.Create("tempAssembly");
    var standardLibraries = new List<string>()
    {
      "DafnyPipeline",
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

  class CollectionErrorReporter : BatchErrorReporter {
    public string GetLastErrorMessage() {
      return allMessages[ErrorLevel.Error][0].message;
    }
  }

  [Fact]
  public async void EnsurePluginIsExecuted() {
    var library = await GetLibrary(@"
using Microsoft.Dafny;
using Microsoft.Dafny.Plugins;

public class TestConfiguration: Configuration {
  public string Argument = """";
  public override void ParseArguments(string[] args) {
    Argument = args[0];
  }
  public override Rewriter[] GetRewriters(ErrorReporter errorReporter) {
    return new Rewriter[]{new ErrorRewriter(errorReporter, this)};
  }
}

public class ErrorRewriter: Rewriter {
  private readonly TestConfiguration configuration;

  public ErrorRewriter(ErrorReporter reporter, TestConfiguration configuration): base(reporter) {
    this.configuration = configuration;
  }

  public override void PostResolve(ModuleDefinition moduleDefinition) {
    Reporter.Error(MessageSource.Compiler, moduleDefinition.tok, ""Impossible to continue ""+configuration.Argument);
  }
}");

    var reporter = new CollectionErrorReporter();
    var options = new DafnyOptions(reporter);
    options.Plugins.Add(new Microsoft.Dafny.Plugin(library, new string[] { "because whatever" }, reporter));
    DafnyOptions.Install(options);

    var programString = "function test(): int { 1 }";
    ModuleDecl module = new LiteralModuleDecl(new DefaultModuleDecl(), null);
    Microsoft.Dafny.Type.ResetScopes();
    BuiltIns builtIns = new BuiltIns();
    Parser.Parse(programString, "virtual", "virtual", module, builtIns, reporter);
    var dafnyProgram = new Program("programName", module, builtIns, reporter);
    Main.Resolve(dafnyProgram, reporter);

    Assert.Equal(1, reporter.Count(ErrorLevel.Error));
    Assert.Equal("Impossible to continue because whatever", reporter.GetLastErrorMessage());
  }

  [Fact]
  public async void EnsurePluginIsExecutedEvenWithoutConfiguration() {
    var library = await GetLibrary(@"
using Microsoft.Dafny;
using Microsoft.Dafny.Plugins;

public class ErrorRewriter: Rewriter {
  public ErrorRewriter(ErrorReporter reporter): base(reporter) {}

  public override void PostResolve(ModuleDefinition moduleDefinition) {
    Reporter.Error(MessageSource.Compiler, moduleDefinition.tok, ""Impossible to continue"");
  }
}");

    var reporter = new CollectionErrorReporter();
    var options = new DafnyOptions(reporter);
    options.Plugins.Add(new Microsoft.Dafny.Plugin(library, new string[] { "ignored arguments" }, reporter));
    DafnyOptions.Install(options);

    var programString = "function test(): int { 1 }";
    ModuleDecl module = new LiteralModuleDecl(new DefaultModuleDecl(), null);
    Microsoft.Dafny.Type.ResetScopes();
    BuiltIns builtIns = new BuiltIns();
    Parser.Parse(programString, "virtual", "virtual", module, builtIns, reporter);
    var dafnyProgram = new Program("programName", module, builtIns, reporter);
    Main.Resolve(dafnyProgram, reporter);

    Assert.Equal(1, reporter.Count(ErrorLevel.Error));
    Assert.Equal("Impossible to continue", reporter.GetLastErrorMessage());
  }
}
