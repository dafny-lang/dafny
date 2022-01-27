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
public class PluginsAdvancedTest : DafnyLanguageServerTestBase {
  private ILanguageClient client;
  private DiagnosticsReceiver diagnosticReceiver;
  private string libraryPath;

  [TestInitialize]
  public async Task SetUp() {
    diagnosticReceiver = new();
    libraryPath = await GetLibrary(@"
using Microsoft.Dafny;
using Microsoft.Dafny.Plugins;
using System.Collections;
/// <summary>
///  Small plugin that detect all extern method and verify that there are test methods that actually invoke them.
/// </summary>
public class TestConfiguration: Configuration {
  public string PluginUser = """";
  public bool ForceName = false;
  public override void ParseArguments(string[] args) {
    ForceName = args.Length > 0 && args[0] == ""force"";
    PluginUser = args.Length > 1 ? "", "" + args[1] : """";
  }
  public override Rewriter[] GetRewriters(ErrorReporter errorReporter) {
    return new Rewriter[]{new ExternCheckRewriter(errorReporter, this)};
  }
}

public class ExternCheckRewriter: Rewriter {
  private readonly TestConfiguration configuration;

  public ExternCheckRewriter(ErrorReporter reporter, TestConfiguration configuration): base(reporter) {
    this.configuration = configuration;
  }

  public override void PostResolve(Program program) {
    foreach (var moduleDefinition in program.Modules()) {
      foreach (var topLevelDecl in moduleDefinition.TopLevelDecls) {
        if (topLevelDecl is ClassDecl cd) {
          foreach (var member in cd.Members) {
            if (member is Method methodExtern) {
              if (Attributes.Contains(member.Attributes, ""extern"")) {
                // Verify that there exists a test method which references this extern method.
                var tested = false;
                Method candidate = null;
                foreach (var member2 in cd.Members) {
                  if (member2 == member || !(member2 is Method methodTest)) {
                    continue;
                  }
                  if (!Attributes.Contains(methodTest.Attributes, ""test"")) {
                    continue;
                  }
                  if (!moduleDefinition.CallGraph.Reaches(methodTest, methodExtern)) {
                    continue;
                  }
                  candidate = methodTest;

                  if (configuration.ForceName && candidate.Name != methodExtern.Name + ""_test"") {
                    continue;
                  }
                  tested = true;
                  break;
                }

                if (!tested) {
                  var forceMessage = configuration.ForceName ? $"" named {methodExtern.Name}_test"" : """";
                  var token = configuration.ForceName && candidate != null
                    ? new NestedToken(methodExtern.tok, candidate.tok, ""You might want to just rename this method"")
                    : methodExtern.tok;
                  Reporter.Error(MessageSource.Resolver, token,
                    $""Please declare a method {{:test}}{forceMessage} that will call {methodExtern.Name}{configuration.PluginUser}"");
                }
              }
            }
          }
        }
      }
    }
  }
}");
    client = await InitializeClient(options => options.OnPublishDiagnostics(diagnosticReceiver.NotificationReceived));
  }

  protected override IConfiguration CreateConfiguration() {
    return new ConfigurationBuilder().AddCommandLine(
      new[] { $@"--dafny:plugins:0=""{libraryPath},force you""" }).Build();
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
      "Boogie.Core",
      "System.Collections"
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
  public async Task EnsureErrorMessageCanBeComplexAndTakeIntoAccountConfiguration() {
    var documentItem = CreateTestDocument(@"
method {:extern} myMethod(i: int) returns (j: int)

method {:test} myMethodWrongName() {
  var result := myMethod(0);
  expect result == 1;
}
");
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
    var resolutionReport = await diagnosticReceiver.AwaitNextNotificationAsync(CancellationToken.None);
    Assert.AreEqual(documentItem.Uri, resolutionReport.Uri);
    var diagnostics = resolutionReport.Diagnostics.ToArray();
    Assert.AreEqual(1, diagnostics.Length);
    Assert.AreEqual("Please declare a method {:test} named myMethod_test that will call myMethod, you", diagnostics[0].Message);
    Assert.AreEqual(new Range((1, 17), (1, 25)), diagnostics[0].Range);
    var related = diagnostics[0].RelatedInformation?.GetEnumerator();
    Assert.IsTrue(related != null && related.MoveNext());
    Assert.AreEqual("You might want to just rename this method", related.Current.Message);
    Assert.AreEqual(new Range((3, 15), (3, 32)), related.Current.Location.Range);
    related.Dispose();
  }
}
