using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using OmniSharp.Extensions.LanguageServer.Protocol.Client;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Various {
  [TestClass]
  public class ConcurrentInteractionsTest : DafnyLanguageServerTestBase {
    private const int MaxTestExecutionTimeMs = 10000;

    private ILanguageClient _client;
    private TestDiagnosticReceiver _diagnosticReceiver;

    [TestInitialize]
    public async Task SetUp() {
      _diagnosticReceiver = new TestDiagnosticReceiver();
      _client = await InitializeClient(options => options.OnPublishDiagnostics(_diagnosticReceiver.DiagnosticReceived));
    }

    [TestMethod, Timeout(MaxTestExecutionTimeMs)]
    public async Task ChangeDocumentRightAfterOpeningCancelsLoad() {
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

      // The initial document does not have issues. If the load was succesfully canceled, we should
      // receive diagnostics with a parser error.
      var report = await _diagnosticReceiver.AwaitNextPublishDiagnostics(CancellationToken);
      var diagnostics = report.Diagnostics.ToArray();
      Assert.AreEqual(0, diagnostics.Length);
    }

    [TestMethod, Timeout(MaxTestExecutionTimeMs)]
    public async Task ChangeDocumentCancelsPreviousChange() {
      var source = @"
lemma {:timeLimit 3} SquareRoot2NotRational(p: nat, q: nat)
  requires p > 0 && q > 0
  ensures (p * p) !=  2 * (q * q)
{ 
  if (p * p) ==  2 * (q * q) {
    calc == {
      (2 * q - p) * (2 * q - p);
      4 * q * q + p * p - 4 * p * q;
      {assert 2 * q * q == p * p;}
      2 * q * q + 2 * p * p - 4 * p * q;
      2 * (p - q) * (p - q);
    }
  }".TrimStart();
      var documentItem = CreateTestDocument(source);
      await _client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var initialLoadReport = await _diagnosticReceiver.AwaitNextPublishDiagnostics(CancellationToken);
      var initialLoadDiagnostics = initialLoadReport.Diagnostics.ToArray();
      Assert.AreEqual(1, initialLoadDiagnostics.Length);

      _client.DidChangeTextDocument(new DidChangeTextDocumentParams {
        TextDocument = new OptionalVersionedTextDocumentIdentifier {
          Uri = documentItem.Uri,
          Version = documentItem.Version + 1
        },
        ContentChanges = new[] {
          new TextDocumentContentChangeEvent {
            Range = new Range((12, 3), (12, 3)),
            Text = "\n}"
          }
        }
      });

      _client.DidChangeTextDocument(new DidChangeTextDocumentParams {
        TextDocument = new OptionalVersionedTextDocumentIdentifier {
          Uri = documentItem.Uri,
          Version = documentItem.Version + 2
        },
        ContentChanges = new[] {
          new TextDocumentContentChangeEvent {
            Range = new Range((0, 0), (13, 1)),
            Text = "function GetConstant(): int { 1 }"
          }
        }
      });

      // The diagnostics of the initial document are already awaited. The original document contains a syntactic error.
      // The first change fixes the error. Therefore, if it was canceled by the second change, it should
      // report the same diagnostics as the initial document (migrated state).
      // The second change replaces the complete document with a correct one. Mind that the original document
      // was chosen because of the exceptionally long time it requires to verify.
      var intermediateReport = await _diagnosticReceiver.AwaitNextPublishDiagnostics(CancellationToken);
      var intermediateDiagnostics = intermediateReport.Diagnostics.ToArray();
      Assert.AreEqual(1, intermediateDiagnostics.Length);
      var report = await _diagnosticReceiver.AwaitNextPublishDiagnostics(CancellationToken);
      var diagnostics = report.Diagnostics.ToArray();
      Assert.AreEqual(0, diagnostics.Length);
    }

    [TestMethod]
    public async Task CanLoadMultipleDocumentsConcurrently() {
      // The current implementation of DafnyLangParser, DafnyLangSymbolResolver, and DafnyProgramVerifier are only mutual
      // exclusive to themselves. This "stress test" ensures that loading multiple documents at once is possible.
      // To be more specific, this test should ensure that there is no state discarded/overriden between the three steps within
      // the Dafny Compiler itself.
      int documentsToLoadConcurrently = 100;
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
      var loadingDocuments = new List<TextDocumentItem>();
      for (int i = 0; i < documentsToLoadConcurrently; i++) {
        var documentItem = CreateTestDocument(source, $"test_{i}.dfy");
        _client.OpenDocument(documentItem);
        loadingDocuments.Add(documentItem);
      }
      for (int i = 0; i < documentsToLoadConcurrently; i++) {
        var report = await _diagnosticReceiver.AwaitNextPublishDiagnostics(CancellationToken);
        Assert.AreEqual(0, report.Diagnostics.Count());
      }
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
        if (_diagnostics.TryDequeue(out var diagnostics)) {
          return diagnostics;
        }
        throw new System.InvalidOperationException("got a signal for a received diagnostic but it was not present in the queue");
      }
    }
  }
}
