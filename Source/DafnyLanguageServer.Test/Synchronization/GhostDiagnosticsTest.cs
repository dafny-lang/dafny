using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using Microsoft.Extensions.Configuration;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using OmniSharp.Extensions.JsonRpc;
using OmniSharp.Extensions.LanguageServer.Protocol.Client;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;
using System.Linq;
using System.Threading.Tasks;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Synchronization {
  [TestClass]
  public class GhostDiagnosticsTest : DafnyLanguageServerTestBase {
    private ILanguageClient client;
    private TestNotificationReceiver<GhostDiagnosticsParams> diagnosticReceiver;
    private IDictionary<string, string> configuration;

    [TestInitialize]
    public Task SetUp() => SetUp(null);

    public async Task SetUp(IDictionary<string, string> configuration) {
      this.configuration = configuration;
      diagnosticReceiver = new();
      client = await InitializeClient(
        options => options.AddHandler(DafnyRequestNames.GhostDiagnostics, NotificationHandler.For<GhostDiagnosticsParams>(diagnosticReceiver.NotificationReceived))
      );
    }

    protected override IConfiguration CreateConfiguration() {
      return configuration == null
        ? base.CreateConfiguration()
        : new ConfigurationBuilder().AddInMemoryCollection(configuration).Build();
    }

    [TestMethod]
    public async Task OpeningFlawlessDocumentWithGhostFadeDeclarationsFadesFunctionDeclaration() {
      var source = @"
function Product(x: nat, y: nat): nat {
  x * y
}

method Multiply(x: int, y: int) returns (product: int)
  requires y >= 0 && x >= 0
  decreases y
  ensures product == Product(x, y) && product >= 0
{
  if y == 0 {
    product := 0;
  } else {
    var step := Multiply(x, y - 1);
    product := x + step;
  }
}".TrimStart();
      await SetUp(new Dictionary<string, string>() {
        { $"{GhostOptions.Section}:{nameof(GhostOptions.FadeDeclarations)}", "true" }
      });
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var report = await diagnosticReceiver.AwaitNextNotificationAsync(CancellationToken);
      var diagnostics = report.Diagnostics.ToArray();
      Assert.AreEqual(1, diagnostics.Length);
      Assert.AreEqual("Ghost function", diagnostics[0].Message);
      Assert.AreEqual(new Range((0, 9), (2, 1)), diagnostics[0].Range);
    }

    [TestMethod]
    public async Task OpeningFlawlessDocumentWithGhostFadeDesignatorsFadesFunctionCall() {
      var source = @"
function Product(x: nat, y: nat): nat {
  x * y
}

method Multiply(x: int, y: int) returns (product: int)
  requires y >= 0 && x >= 0
  decreases y
  ensures product == Product(x, y) && product >= 0
{
  if y == 0 {
    product := 0;
  } else {
    var step := Multiply(x, y - 1);
    product := x + step;
  }
}".TrimStart();
      await SetUp(new Dictionary<string, string>() {
        { $"{GhostOptions.Section}:{nameof(GhostOptions.FadeDesignators)}", "true" }
      });
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var report = await diagnosticReceiver.AwaitNextNotificationAsync(CancellationToken);
      var diagnostics = report.Diagnostics.ToArray();
      Assert.AreEqual(1, diagnostics.Length);
      Assert.AreEqual("Ghost function", diagnostics[0].Message);
      Assert.AreEqual(new Range((7, 21), (7, 28)), diagnostics[0].Range);
    }

    [TestMethod]
    public async Task OpeningFlawlessDocumentWithGhostFadeDesignatorsFadesVariableName() {
      var source = @"
method Multiply(x: int, y: int) returns (product: int)
  requires y >= 0 && x >= 0
  decreases y
  ensures product == x * y && product >= 0
{
  ghost var z := 0;
  if y == 0 {
    product := 0;
  } else {
    var step := Multiply(x, y - 1);
    product := x + step;
  }
  z := -1;
}".TrimStart();
      await SetUp(new Dictionary<string, string>() {
        { $"{GhostOptions.Section}:{nameof(GhostOptions.FadeDesignators)}", "true" }
      });
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var report = await diagnosticReceiver.AwaitNextNotificationAsync(CancellationToken);
      var diagnostics = report.Diagnostics.ToArray();
      Assert.AreEqual(2, diagnostics.Length);
      Assert.AreEqual("Ghost variable", diagnostics[0].Message);
      Assert.AreEqual(new Range((5, 12), (5, 13)), diagnostics[0].Range);
      Assert.AreEqual("Ghost variable", diagnostics[1].Message);
      Assert.AreEqual(new Range((12, 2), (12, 3)), diagnostics[1].Range);
    }

    [TestMethod]
    public async Task OpeningFlawlessDocumentWithGhostFadeStatementsFadesGhostVariableDeclarationsAndAssignments() {
      var source = @"
method Multiply(x: int, y: int) returns (product: int)
  requires y >= 0 && x >= 0
  decreases y
  ensures product == x * y && product >= 0
{
  ghost var z := 0;
  if y == 0 {
    product := 0;
  } else {
    var step := Multiply(x, y - 1);
    product := x + step;
  }
  z := -1;
}".TrimStart();
      await SetUp(new Dictionary<string, string>() {
        { $"{GhostOptions.Section}:{nameof(GhostOptions.FadeStatements)}", "true" }
      });
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var report = await diagnosticReceiver.AwaitNextNotificationAsync(CancellationToken);
      var diagnostics = report.Diagnostics.ToArray();
      Assert.AreEqual(2, diagnostics.Length);
      Assert.AreEqual("Ghost statement", diagnostics[0].Message);
      Assert.AreEqual(new Range((5, 2), (5, 18)), diagnostics[0].Range);
      Assert.AreEqual("Ghost statement", diagnostics[1].Message);
      Assert.AreEqual(new Range((12, 4), (12, 9)), diagnostics[1].Range);
    }
  }
}
