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
public class ExternalResolverTest : DafnyLanguageServerTestBase {
  private ILanguageClient client;
  private DiagnosticsReceiver diagnosticReceiver;
  private Assembly library;

  [TestInitialize]
  public async Task SetUp() {
    diagnosticReceiver = new();
    library = await GetLibrary(@"
      using Microsoft.Dafny;
      public class ErrorRewriter: IRewriter {
        public ErrorRewriter(ErrorReporter reporter) : base(reporter)
        {}

        public override void PostResolve(ModuleDefinition m) {
          reporter.Error(MessageSource.Compiler, m.tok, ""Impossible to continue"");
        }
      }");
    client = await InitializeClient(options => options.OnPublishDiagnostics(diagnosticReceiver.NotificationReceived));
  }

  protected override IConfiguration CreateConfiguration() {
    return new ConfigurationBuilder().AddCommandLine(
      new[] { "--dafny:plugins=" + this.library.Location }).Build();
  }

  /// <summary>
  /// This method creates a library and returns the path to that library.
  /// The library extends an IRewriter so that we can verify that Dafny invokes it if provided in argument.
  /// </summary>
  public async Task<Assembly> GetLibrary(string code) {
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
    return Assembly.LoadFrom(assemblyPath);
  }

  [TestMethod]
  public async Task EnsureItIsPossibleToPluginIRewriter() {
    var documentItem = CreateTestDocument("function test(): int { 1 }");
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
    var resolutionReport = await diagnosticReceiver.AwaitNextNotificationAsync(CancellationToken.None);
    Assert.AreEqual(documentItem.Uri, resolutionReport.Uri);
    var diagnostics = resolutionReport.Diagnostics.ToArray();
    Assert.AreEqual(1, diagnostics.Length);
    Assert.AreEqual("Impossible to continue", diagnostics[0].Message);
    Assert.AreEqual(new Range((-1, -1), (-1, 29)), diagnostics[0].Range);
  }
}