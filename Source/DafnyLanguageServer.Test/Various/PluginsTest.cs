using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Reflection;
using System.Threading.Tasks;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using System;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using System.Collections.Generic;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Microsoft.Extensions.Configuration;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Client;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Various;

[TestClass]
public class PluginsTest : DafnyLanguageServerTestBase {
  private ILanguageClient client;
  private DiagnosticsReceiver diagnosticReceiver;
  private string libraryPath;

  [TestInitialize]
  public async Task SetUp() {
    diagnosticReceiver = new();
    libraryPath = await GetLibrary(@"
using Microsoft.Dafny;
using Microsoft.Dafny.Plugins;

public class TestConfiguration: Configuration {
  public string Argument = """";
  public override void ParseArguments(string[] args) {
    Argument = args.Length > 0 ? args[0] : ""[no argument]"";
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
    Reporter.Error(MessageSource.Compiler, moduleDefinition.GetFirstTopLevelToken(), ""Impossible to continue ""+configuration.Argument);
  }
}");
    client = await InitializeClient(options => options.OnPublishDiagnostics(diagnosticReceiver.NotificationReceived));
  }

  protected override IConfiguration CreateConfiguration() {
    return new ConfigurationBuilder().AddCommandLine(
      new[] { $@"--dafny:plugins:0=""{libraryPath},\""because\\ whatever\""""" }).Build();
  }

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

    Assert.IsTrue(result.Success, string.Join("\n", result.Diagnostics.Select(d => d.ToString())));
    return assemblyPath;
  }

  [TestMethod]
  public async Task EnsureItIsPossibleToLoadAPluginWithArguments() {
    var documentItem = CreateTestDocument("function test(): int { 1 }");
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
    var resolutionReport = await diagnosticReceiver.AwaitNextNotificationAsync(CancellationToken.None);
    Assert.AreEqual(documentItem.Uri, resolutionReport.Uri);
    var diagnostics = resolutionReport.Diagnostics.ToArray();
    Assert.AreEqual(1, diagnostics.Length);
    Assert.AreEqual("Impossible to continue because\\ whatever", diagnostics[0].Message);
    Assert.AreEqual(new Range((0, 9), (0, 13)), diagnostics[0].Range);
  }
}
