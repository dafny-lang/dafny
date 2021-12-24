using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using OmniSharp.Extensions.LanguageServer.Protocol.Client;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Various {
  [TestClass]
  public class ConcurrentInteractionsTest : DafnyLanguageServerTestBase {
    // Implementation note: These tests assume that no diagnostics are published
    // when a document (re-load) was canceled (DafnyDocument.LoadCanceled).
    private const int MaxTestExecutionTimeMs = 240_000;
    private const int MaxRequestExecutionTimeMs = 180_000;

    private ILanguageClient client;
    private DiagnosticsReceiver diagnosticReceiver;

    // We do not use the LanguageServerTestBase.cancellationToken here because it has a timeout.
    // Since these tests are slow, we do not use the timeout here.
    private CancellationTokenSource cancellationSource;
    private CancellationToken CancellationTokenWithHighTimeout => cancellationSource.Token;

    [TestInitialize]
    public async Task SetUp() {
      diagnosticReceiver = new();
      client = await InitializeClient(options => options.OnPublishDiagnostics(diagnosticReceiver.NotificationReceived));
      // We use a custom cancellation token with a higher timeout to clearly identify where the request got stuck.
      cancellationSource = new();
      cancellationSource.CancelAfter(MaxRequestExecutionTimeMs);
    }

    [TestMethod, Timeout(MaxTestExecutionTimeMs)]
    public async Task ResolutionDiagnosticsContainPreviousVerificationResults() {
      var fastToVerify = "function GetConstant(): int ensures false { 1 }";
      var slowToVerify = @"
lemma {:timeLimit 10} SquareRoot2NotRational(p: nat, q: nat)
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
  }
}";

      var documentItem = CreateTestDocument(fastToVerify);
      client.OpenDocument(documentItem);
      var verificationDiagnostics = await diagnosticReceiver.AwaitVerificationDiagnosticsAsync(CancellationToken);
      Assert.AreEqual(1, verificationDiagnostics.Length);
      ApplyChange(documentItem, new Range(0, 0, 0, 0), slowToVerify + "\n\n");
      var resolutionDiagnostics = await diagnosticReceiver.AwaitNextDiagnosticsAsync(CancellationToken);
      Assert.AreEqual(1, resolutionDiagnostics.Length);
      // Verification diagnostic should have been moved.
      Assert.AreEqual(16, resolutionDiagnostics[0].Range.Start.Line);
    }

    [TestMethod, Timeout(MaxTestExecutionTimeMs)]
    public async Task ChangeDocumentCancelsPreviousOpenAndChangeVerification() {
      var source = @"
lemma {:timeLimit 10} SquareRoot2NotRational(p: nat, q: nat)
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
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationTokenWithHighTimeout);
      // The original document contains a syntactic error.
      var initialLoadDiagnostics = await diagnosticReceiver.AwaitNextDiagnosticsAsync(CancellationTokenWithHighTimeout);
      Assert.IsFalse(await diagnosticReceiver.AreMoreDiagnosticsComing());
      Assert.AreEqual(1, initialLoadDiagnostics.Length);

      client.DidChangeTextDocument(new DidChangeTextDocumentParams {
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

      // Wait for resolution diagnostics now, so they don't get cancelled.
      var parseErrorFixedDiagnostics = await diagnosticReceiver.AwaitNextDiagnosticsAsync(CancellationTokenWithHighTimeout);
      Assert.AreEqual(0, parseErrorFixedDiagnostics.Length);

      await client.ChangeDocumentAndWaitAsync(new DidChangeTextDocumentParams {
        TextDocument = new OptionalVersionedTextDocumentIdentifier {
          Uri = documentItem.Uri,
          Version = documentItem.Version + 2
        },
        ContentChanges = new[] {
          new TextDocumentContentChangeEvent {
            Range = new Range((0, 0), (13, 1)),
            Text = "function GetConstant(): int ensures false { 1 }"
          }
        }
      }, CancellationTokenWithHighTimeout);

      var parseErrorStillFixedDiagnostics = await diagnosticReceiver.AwaitNextDiagnosticsAsync(CancellationTokenWithHighTimeout);
      Assert.AreEqual(0, parseErrorStillFixedDiagnostics.Length);

      var verificationDiagnostics = await diagnosticReceiver.AwaitNextDiagnosticsAsync(CancellationTokenWithHighTimeout);
      Assert.AreEqual(1, verificationDiagnostics.Length);

      Assert.IsFalse(await diagnosticReceiver.AreMoreDiagnosticsComing());
    }

    /// <summary>
    /// If this test is flaky, increase the amount of lines in the source program
    /// </summary>
    [TestMethod, Timeout(MaxTestExecutionTimeMs)]
    public async Task ChangeDocumentCancelsPreviousResolution() {
      // Two syntax errors
      var createCorrectFunction = (int index) => @$"function GetConstant{index}(x: int): int {{ x }}";
      var functionWithError = "function GetConstant(): int { x }\n";
      var slowToResolveSource = functionWithError + string.Join("\n", Enumerable.Range(0, 1000).Select(createCorrectFunction));
      var documentItem = CreateTestDocument(slowToResolveSource);
      client.OpenDocument(documentItem);

      // Change but keep a resolution error, cancel previous diagnostics
      documentItem = ApplyChange(documentItem, new Range((0, 30), (0, 31)), "y");

      // Fix resolution error, cancel previous diagnostics
      ApplyChange(documentItem, new Range((0, 30), (0, 31)), "1");

      var resolutionDiagnostics = await diagnosticReceiver.AwaitNextDiagnosticsAsync(CancellationToken);
      Assert.AreEqual(0, resolutionDiagnostics.Length);

      var verificationDiagnostics = await diagnosticReceiver.AwaitNextDiagnosticsAsync(CancellationToken);
      Assert.AreEqual(0, verificationDiagnostics.Length);

      Assert.IsFalse(await diagnosticReceiver.AreMoreDiagnosticsComing());
    }

    private TextDocumentItem ApplyChange(TextDocumentItem documentItem, Range range, string text) {
      var result = documentItem with { Version = documentItem.Version + 1 };
      client.DidChangeTextDocument(new DidChangeTextDocumentParams {
        TextDocument = new OptionalVersionedTextDocumentIdentifier {
          Uri = documentItem.Uri,
          Version = result.Version
        },
        ContentChanges = new[] {
          new TextDocumentContentChangeEvent {
            Range = range,
            Text = text
          }
        }
      });
      return result;
    }

    [TestMethod, Timeout(MaxTestExecutionTimeMs)]
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
        client.OpenDocument(documentItem);
        loadingDocuments.Add(documentItem);
      }
      for (int i = 0; i < documentsToLoadConcurrently; i++) {
        var report = await diagnosticReceiver.AwaitNextNotificationAsync(CancellationTokenWithHighTimeout);
        Assert.AreEqual(0, report.Diagnostics.Count());
      }
    }
  }
}
