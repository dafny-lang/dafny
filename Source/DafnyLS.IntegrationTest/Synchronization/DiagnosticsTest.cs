using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using OmniSharp.Extensions.LanguageServer.Protocol.Client;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Concurrent;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Synchronization {
  [TestClass]
  public class DiagnosticsTest : DafnyLanguageServerTestBase {
    // TODO test locations as well?
    private ILanguageClient _client;
    private TestDiagnosticReceiver _diagnosticReceiver;

    [TestInitialize]
    public async Task SetUp() {
      _diagnosticReceiver = new TestDiagnosticReceiver();
      _client = await InitializeClient(options => options.OnPublishDiagnostics(_diagnosticReceiver.DiagnosticReceived));
    }

    [TestMethod]
    public async Task OpeningFlawlessDocumentReportsEmptyDiagnostics() {
      var source = @"
method Multiply(x: int, y: int) returns (product: int)
  requires y >= 0 && x >= 0
  decreases y
  ensures product == x * y && product >= 0
{
  if y == 0 {
    product := 0;
  } else {
    var step := Multiply(x, y - 1);
    product := x + step;
  }
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      _client.OpenDocument(documentItem);
      var report = await _diagnosticReceiver.AwaitNextPublishDiagnostics(CancellationToken);
      var diagnostics = report.Diagnostics.ToArray();
      Assert.AreEqual(0, diagnostics.Length);
    }

    [TestMethod]
    public async Task OpeningDocumentWithSyntaxErrorReportsDiagnosticsWithParserErrors() {
      var source = @"
method Multiply(x: int, y: int) returns (product: int
  requires y >= 0 && x >= 0
  decreases y
  ensures product == x * y && product >= 0
{
  if y == 0 {
    product := 0;
  } else {
    var step := Multiply(x, y - 1);
    product := x + step;
  }
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      _client.OpenDocument(documentItem);
      var report = await _diagnosticReceiver.AwaitNextPublishDiagnostics(CancellationToken);
      var diagnostics = report.Diagnostics.ToArray();
      Assert.AreEqual(1, diagnostics.Length);
      Assert.AreEqual("Parser", diagnostics[0].Source);
      Assert.AreEqual(DiagnosticSeverity.Error, diagnostics[0].Severity);
    }

    [TestMethod]
    public async Task OpeningDocumentWithSemanticErrorReportsDiagnosticsWithSemanticErrors() {
      var source = @"
method Multiply(x: int, y: int) returns (product: int)
  requires y >= 0 && x >= 0
  decreases y
  ensures product == x * y && product >= 0
{
  if y == 0 {
    product := 0;
  } else {
    var step := Multiply(x, y - ""1"");
    product := x + step;
  }
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      _client.OpenDocument(documentItem);
      var report = await _diagnosticReceiver.AwaitNextPublishDiagnostics(CancellationToken);
      var diagnostics = report.Diagnostics.ToArray();
      Assert.AreEqual(1, diagnostics.Length);
      Assert.AreEqual("Resolver", diagnostics[0].Source);
      Assert.AreEqual(DiagnosticSeverity.Error, diagnostics[0].Severity);
    }

    [TestMethod]
    public async Task OpeningDocumentWithMultipleSemanticErrorsReportsDiagnosticsWithAllSemanticErrors() {
      var source = @"
method Multiply(x: int, y: int) returns (product: int)
  requires y >= 0 && x >= 0
  decreases y
  ensures product == x * y && product >= 0
{
  if y == ""0"" {
    product := 0;
  } else {
    var step := Multiply(x, y - ""1"");
    product := x + step;
  }
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      _client.OpenDocument(documentItem);
      var report = await _diagnosticReceiver.AwaitNextPublishDiagnostics(CancellationToken);
      var diagnostics = report.Diagnostics.ToArray();
      Assert.AreEqual(2, diagnostics.Length);
      Assert.AreEqual("Resolver", diagnostics[0].Source);
      Assert.AreEqual(DiagnosticSeverity.Error, diagnostics[0].Severity);
      Assert.AreEqual("Resolver", diagnostics[1].Source);
      Assert.AreEqual(DiagnosticSeverity.Error, diagnostics[1].Severity);
    }

    [TestMethod]
    public async Task OpeningDocumentWithVerificationErrorReportsDiagnosticsWithVerificationErrors() {
      var source = @"
method Multiply(x: int, y: int) returns (product: int)
  requires x >= 0
  decreases y
  ensures product == x * y && product >= 0
{
  if y == 0 {
    product := 0;
  } else {
    var step := Multiply(x, y - 1);
    product := x + step;
  }
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      _client.OpenDocument(documentItem);
      var report = await _diagnosticReceiver.AwaitNextPublishDiagnostics(CancellationToken);
      var diagnostics = report.Diagnostics.ToArray();
      Assert.AreEqual(1, diagnostics.Length);
      Assert.AreEqual("Other", diagnostics[0].Source);
      Assert.AreEqual(DiagnosticSeverity.Error, diagnostics[0].Severity);
    }

    [TestMethod]
    public async Task OpeningDocumentWithMultipleVerificationErrorsReportsDiagnosticsWithAllVerificationErrors() {
      var source = @"
method Multiply(x: int, y: int) returns (product: int)
  decreases y
  ensures product == x * y && product >= 0
{
  if y == 0 {
    product := 0;
  } else {
    var step := Multiply(x, y - 1);
    product := x + step;
  }
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      _client.OpenDocument(documentItem);
      var report = await _diagnosticReceiver.AwaitNextPublishDiagnostics(CancellationToken);
      var diagnostics = report.Diagnostics.ToArray();
      Assert.AreEqual(3, diagnostics.Length);
      Assert.AreEqual("Other", diagnostics[0].Source);
      Assert.AreEqual(DiagnosticSeverity.Error, diagnostics[0].Severity);
      Assert.AreEqual("Other", diagnostics[1].Source);
      Assert.AreEqual(DiagnosticSeverity.Error, diagnostics[1].Severity);
      Assert.AreEqual("Other", diagnostics[2].Source);
      Assert.AreEqual(DiagnosticSeverity.Information, diagnostics[2].Severity);
    }

    [TestMethod]
    public async Task ChangingCorrectDocumentToOneWithSyntaxErrorsReportsTheSyntaxErrors() {
      var source = @"
method Multiply(x: int, y: int) returns (product: int)
  requires y >= 0 && x >= 0
  decreases y
  ensures product == x * y && product >= 0
{
  if y == 0 {
    product := 0;
  } else {
    var step := Multiply(x, y - 1);
    product := x + step;
  }
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      _client.OpenDocument(documentItem);
      var reportAfterOpening = await _diagnosticReceiver.AwaitNextPublishDiagnostics(CancellationToken);
      var diagnosticsAfterOpening = reportAfterOpening.Diagnostics.ToArray();
      Assert.AreEqual(0, diagnosticsAfterOpening.Length);

      _client.DidChangeTextDocument(new DidChangeTextDocumentParams {
        TextDocument = new VersionedTextDocumentIdentifier {
          Uri = documentItem.Uri,
          Version = documentItem.Version + 1
        },
        ContentChanges = new[] {
          new TextDocumentContentChangeEvent {
            Range = new Range((0, 53), (0, 54)),
            Text = ""
          }
        }
      });


      var report = await _diagnosticReceiver.AwaitNextPublishDiagnostics(CancellationToken);
      var diagnostics = report.Diagnostics.ToArray();
      Assert.AreEqual(1, diagnostics.Length);
      Assert.AreEqual("Parser", diagnostics[0].Source);
      Assert.AreEqual(DiagnosticSeverity.Error, diagnostics[0].Severity);
    }

    [TestMethod]
    public async Task ApplyingMultipleChangesInDocumentOnlySendsOneReport() {
      var source = @"
method Multiply(x: int, y: int) returns (product: int)
  requires y >= 0 && x >= 0
  decreases y
  ensures product == x * y && product >= 0
{
  if y == 0 {
    product := 0;
  } else {
    var step := Multiply(x, y - 1);
    product := x + step;
  }
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      _client.OpenDocument(documentItem);
      var reportAfterOpening = await _diagnosticReceiver.AwaitNextPublishDiagnostics(CancellationToken);
      var diagnosticsAfterOpening = reportAfterOpening.Diagnostics.ToArray();
      Assert.AreEqual(0, diagnosticsAfterOpening.Length);

      _client.DidChangeTextDocument(new DidChangeTextDocumentParams {
        TextDocument = new VersionedTextDocumentIdentifier {
          Uri = documentItem.Uri,
          Version = documentItem.Version + 1
        },
        ContentChanges = new[] {
          new TextDocumentContentChangeEvent {
            Range = new Range((0, 53), (0, 54)),
            Text = ""
          },
          new TextDocumentContentChangeEvent {
            Range = new Range((0, 53), (0, 53)),
            Text = ")"
          }
        }
      });

      // The test applies a change that introduces a syntax error and fixes it thereafter.
      // Therefore, we know that the erronoues state was never reported when we now receive
      // a report without any diagnostics/errors.
      // Otherwise, we'd have to wait for a signal/diagnostic that should never be sent, e.g.
      // with a timeout.
      var report = await _diagnosticReceiver.AwaitNextPublishDiagnostics(CancellationToken);
      var diagnostics = report.Diagnostics.ToArray();
      Assert.AreEqual(0, diagnostics.Length);
    }

    [TestMethod]
    public async Task ClosingDocumentWithSyntaxErrorHidesDiagnosticsBySendingEmptyDiagnostics() {
      var source = @"
method Multiply(x: int, y: int) returns (product: int
  requires y >= 0 && x >= 0
  decreases y
  ensures product == x * y && product >= 0
{
  if y == 0 {
    product := 0;
  } else {
    var step := Multiply(x, y - 1);
    product := x + step;
  }
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      _client.OpenDocument(documentItem);
      await _diagnosticReceiver.AwaitNextPublishDiagnostics(CancellationToken);
      _client.DidCloseTextDocument(new DidCloseTextDocumentParams { TextDocument = documentItem });
      var report = await _diagnosticReceiver.AwaitNextPublishDiagnostics(CancellationToken);
      var diagnostics = report.Diagnostics.ToArray();
      Assert.AreEqual(0, diagnostics.Length);
    }

    public class TestDiagnosticReceiver {
      private readonly SemaphoreSlim _availableDiagnostics = new SemaphoreSlim(0);
      private readonly ConcurrentQueue<PublishDiagnosticsParams> _diagnostics = new ConcurrentQueue<PublishDiagnosticsParams>();

      public void DiagnosticReceived(PublishDiagnosticsParams request) {
        _diagnostics.Enqueue(request);
        _availableDiagnostics.Release();
      }

      public async Task<PublishDiagnosticsParams> AwaitNextPublishDiagnostics(CancellationToken cancellationToken) {
        await _availableDiagnostics.WaitAsync(cancellationToken);
        if(_diagnostics.TryDequeue(out var diagnostics)) {
          return diagnostics;
        }
        throw new System.InvalidOperationException("got a signal for a received diagnostic but it was not present in the queue");
      }
    }
  }
}
