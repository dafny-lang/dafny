using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Extensions.Configuration;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using OmniSharp.Extensions.LanguageServer.Protocol.Client;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Synchronization {
  [TestClass]
  public class DiagnosticsTest : DafnyLanguageServerTestBase {
    // TODO test locations as well?
    private ILanguageClient _client;
    private TestDiagnosticReceiver _diagnosticReceiver;
    private IDictionary<string, string> _configuration;

    [TestInitialize]
    public Task SetUp() => SetUp(null);

    public async Task SetUp(IDictionary<string, string> configuration) {
      _configuration = configuration;
      _diagnosticReceiver = new TestDiagnosticReceiver();
      _client = await InitializeClient(options => options.OnPublishDiagnostics(_diagnosticReceiver.DiagnosticReceived));
    }

    protected override IConfiguration CreateConfiguration() {
      return _configuration == null
        ? base.CreateConfiguration()
        : new ConfigurationBuilder().AddInMemoryCollection(_configuration).Build();
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
    public async Task OpeningDocumentWithVerificationErrorDoesNotReportDiagnosticsWithVerificationErrorsIfNotVerifyOnChange() {
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
      await SetUp(new Dictionary<string, string>() {
        { $"{DocumentOptions.Section}:{nameof(DocumentOptions.Verify)}", nameof(AutoVerification.Never) }
      });
      var documentItem = CreateTestDocument(source);
      _client.OpenDocument(documentItem);
      var report = await _diagnosticReceiver.AwaitNextPublishDiagnostics(CancellationToken);
      var diagnostics = report.Diagnostics.ToArray();
      Assert.AreEqual(0, diagnostics.Length);
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
        TextDocument = new OptionalVersionedTextDocumentIdentifier {
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
    public async Task ChangingCorrectDocumentToOneWithSyntaxErrorsReportsTheSyntaxErrorsIfNotVerifyOnChange() {
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
      await SetUp(new Dictionary<string, string>() {
        { $"{DocumentOptions.Section}:{nameof(DocumentOptions.Verify)}", nameof(AutoVerification.Never) }
      });
      var documentItem = CreateTestDocument(source);
      _client.OpenDocument(documentItem);
      var reportAfterOpening = await _diagnosticReceiver.AwaitNextPublishDiagnostics(CancellationToken);
      var diagnosticsAfterOpening = reportAfterOpening.Diagnostics.ToArray();
      Assert.AreEqual(0, diagnosticsAfterOpening.Length);

      _client.DidChangeTextDocument(new DidChangeTextDocumentParams {
        TextDocument = new OptionalVersionedTextDocumentIdentifier {
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
    public async Task ChangingCorrectDocumentToOneWithVerificationErrorsReportsTheVerificationErrors() {
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
        TextDocument = new OptionalVersionedTextDocumentIdentifier {
          Uri = documentItem.Uri,
          Version = documentItem.Version + 1
        },
        ContentChanges = new[] {
          new TextDocumentContentChangeEvent {
            Range = new Range((8, 30), (8, 31)),
            Text = "+"
          }
        }
      });

      var report = await _diagnosticReceiver.AwaitNextPublishDiagnostics(CancellationToken);
      var diagnostics = report.Diagnostics.ToArray();
      Assert.AreEqual(1, diagnostics.Length);
      Assert.AreEqual("Other", diagnostics[0].Source);
      Assert.AreEqual(DiagnosticSeverity.Error, diagnostics[0].Severity);
    }

    [TestMethod]
    public async Task ChangingCorrectDocumentToOneWithVerificationErrorsDoesNotReportVerificationErrorsIfNotVerifyOnChange() {
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
      await SetUp(new Dictionary<string, string>() {
        { $"{DocumentOptions.Section}:{nameof(DocumentOptions.Verify)}", nameof(AutoVerification.Never) }
      });
      var documentItem = CreateTestDocument(source);
      _client.OpenDocument(documentItem);
      var reportAfterOpening = await _diagnosticReceiver.AwaitNextPublishDiagnostics(CancellationToken);
      var diagnosticsAfterOpening = reportAfterOpening.Diagnostics.ToArray();
      Assert.AreEqual(0, diagnosticsAfterOpening.Length);

      _client.DidChangeTextDocument(new DidChangeTextDocumentParams {
        TextDocument = new OptionalVersionedTextDocumentIdentifier {
          Uri = documentItem.Uri,
          Version = documentItem.Version + 1
        },
        ContentChanges = new[] {
          new TextDocumentContentChangeEvent {
            Range = new Range((8, 30), (8, 31)),
            Text = "+"
          }
        }
      });

      var report = await _diagnosticReceiver.AwaitNextPublishDiagnostics(CancellationToken);
      var diagnostics = report.Diagnostics.ToArray();
      Assert.AreEqual(0, diagnostics.Length);
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
        TextDocument = new OptionalVersionedTextDocumentIdentifier {
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

    [TestMethod]
    public async Task OpeningDocumentThatIncludesNonExistantDocumentReportsParserErrorAtInclude() {
      var source = "include \"doesNotExist.dfy\"";
      var documentItem = CreateTestDocument(source, Path.Combine(Directory.GetCurrentDirectory(), "Synchronization/TestFiles/test.dfy"));
      _client.OpenDocument(documentItem);
      var report = await _diagnosticReceiver.AwaitNextPublishDiagnostics(CancellationToken);
      var diagnostics = report.Diagnostics.ToArray();
      Assert.AreEqual(1, diagnostics.Length);
      Assert.AreEqual("Parser", diagnostics[0].Source);
      Assert.AreEqual(DiagnosticSeverity.Error, diagnostics[0].Severity);
      Assert.AreEqual(new Range((0, 8), (0, 26)), diagnostics[0].Range);
    }

    [TestMethod]
    public async Task OpeningDocumentThatIncludesDocumentWithSyntaxErrorsReportsParserErrorAtInclude() {
      var source = "include \"syntaxError.dfy\"";
      var documentItem = CreateTestDocument(source, Path.Combine(Directory.GetCurrentDirectory(), "Synchronization/TestFiles/test.dfy"));
      _client.OpenDocument(documentItem);
      var report = await _diagnosticReceiver.AwaitNextPublishDiagnostics(CancellationToken);
      var diagnostics = report.Diagnostics.ToArray();
      Assert.AreEqual(1, diagnostics.Length);
      Assert.AreEqual("Parser", diagnostics[0].Source);
      Assert.AreEqual(DiagnosticSeverity.Error, diagnostics[0].Severity);
      Assert.AreEqual(new Range((0, 8), (0, 25)), diagnostics[0].Range);
    }

    [TestMethod]
    public async Task OpeningDocumentThatIncludesDocumentWithSemanticErrorsReportsResolverErrorAtInclude() {
      var source = "include \"syntaxError.dfy\"";
      var documentItem = CreateTestDocument(source, Path.Combine(Directory.GetCurrentDirectory(), "Synchronization/TestFiles/test.dfy"));
      _client.OpenDocument(documentItem);
      var report = await _diagnosticReceiver.AwaitNextPublishDiagnostics(CancellationToken);
      var diagnostics = report.Diagnostics.ToArray();
      Assert.AreEqual(1, diagnostics.Length);
      Assert.AreEqual("Parser", diagnostics[0].Source);
      Assert.AreEqual(DiagnosticSeverity.Error, diagnostics[0].Severity);
      Assert.AreEqual(new Range((0, 8), (0, 25)), diagnostics[0].Range);
    }

    [TestMethod]
    public async Task OpeningDocumentWithSemanticErrorsInIncludeReportsResolverErrorAtIncludeStatement() {
      var source = "include \"semanticError.dfy\"";
      var documentItem = CreateTestDocument(source, Path.Combine(Directory.GetCurrentDirectory(), "Synchronization/TestFiles/test.dfy"));
      _client.OpenDocument(documentItem);
      var report = await _diagnosticReceiver.AwaitNextPublishDiagnostics(CancellationToken);
      var diagnostics = report.Diagnostics.ToArray();
      Assert.AreEqual(1, diagnostics.Length);
      Assert.AreEqual("Resolver", diagnostics[0].Source);
      Assert.AreEqual(DiagnosticSeverity.Error, diagnostics[0].Severity);
      Assert.AreEqual(new Range((0, 8), (0, 27)), diagnostics[0].Range);
    }

    [TestMethod]
    public async Task SavingDocumentWithVerificationErrorDoesNotDiscardDiagnosticsWithVerificationErrorsIfVerifyOnChange() {
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
      var changeReport = await _diagnosticReceiver.AwaitNextPublishDiagnostics(CancellationToken);
      var changeDiagnostics = changeReport.Diagnostics.ToArray();
      Assert.AreEqual(1, changeDiagnostics.Length);
      Assert.AreEqual("Other", changeDiagnostics[0].Source);
      Assert.AreEqual(DiagnosticSeverity.Error, changeDiagnostics[0].Severity);
      _client.SaveDocument(documentItem);
      var saveReport = await _diagnosticReceiver.AwaitNextPublishDiagnostics(CancellationToken);
      var saveDiagnostics = saveReport.Diagnostics.ToArray();
      Assert.AreEqual(1, saveDiagnostics.Length);
      Assert.AreEqual("Other", saveDiagnostics[0].Source);
      Assert.AreEqual(DiagnosticSeverity.Error, saveDiagnostics[0].Severity);
    }

    [TestMethod]
    public async Task SavingDocumentWithVerificationErrorReportsDiagnosticsWithVerificationErrorsIfVerifyOnSave() {
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
      await SetUp(new Dictionary<string, string>() {
        { $"{DocumentOptions.Section}:{nameof(DocumentOptions.Verify)}", nameof(AutoVerification.OnSave) }
      });
      var documentItem = CreateTestDocument(source);
      _client.OpenDocument(documentItem);
      var changeReport = await _diagnosticReceiver.AwaitNextPublishDiagnostics(CancellationToken);
      var changeDiagnostics = changeReport.Diagnostics.ToArray();
      Assert.AreEqual(0, changeDiagnostics.Length);
      _client.SaveDocument(documentItem);
      var saveReport = await _diagnosticReceiver.AwaitNextPublishDiagnostics(CancellationToken);
      var saveDiagnostics = saveReport.Diagnostics.ToArray();
      Assert.AreEqual(1, saveDiagnostics.Length);
      Assert.AreEqual("Other", saveDiagnostics[0].Source);
      Assert.AreEqual(DiagnosticSeverity.Error, saveDiagnostics[0].Severity);
    }

    public class TestDiagnosticReceiver {
      private readonly SemaphoreSlim _availableDiagnostics = new(0);
      private readonly ConcurrentQueue<PublishDiagnosticsParams> _diagnostics = new();

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
