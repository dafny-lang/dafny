using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using OmniSharp.Extensions.LanguageServer.Protocol.Client;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Extensions.Configuration;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Various {
  [TestClass]
  public class ConcurrentInteractionsTest : DafnyLanguageServerTestBase {
    // Implementation note: These tests assume that no diagnostics are published
    // when a document (re-load) was canceled (DafnyDocument.LoadCanceled).
    private const int MaxTestExecutionTimeMs = 240_000;
    private const int MaxRequestExecutionTimeMs = 180_000;

    private ILanguageClient client;
    private IDictionary<string, string> configuration;
    private TestNotificationReceiver<PublishDiagnosticsParams> diagnosticReceiver;

    // We do not use the LanguageServerTestBase.cancellationToken here because it has a timeout.
    // Since these tests are slow, we do not use the timeout here.
    private CancellationTokenSource cancellationSource;
    private CancellationToken CancellationTokenWithHighTimeout => cancellationSource.Token;

    [TestInitialize]
    public Task SetUp() => SetUp(null);

    public async Task SetUp(IDictionary<string, string> configuration) {
      this.configuration = configuration;
      diagnosticReceiver = new();
      client = await InitializeClient(options => options.OnPublishDiagnostics(diagnosticReceiver.NotificationReceived));
      // We use a custom cancellation token with a higher timeout to clearly identify where the request got stuck.
      cancellationSource = new();
      cancellationSource.CancelAfter(MaxRequestExecutionTimeMs);
    }
    protected override IConfiguration CreateConfiguration() {
      return configuration == null
        ? base.CreateConfiguration()
        : new ConfigurationBuilder().AddInMemoryCollection(configuration).Build();
    }

    [TestMethod, Timeout(MaxTestExecutionTimeMs), Ignore("Disabled due to instability since the verification cannot always be canceled.")]
    public async Task ChangeDocumentRightAfterOpeningCancelsLoad() {
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
  }
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      client.OpenDocument(documentItem);
      await client.ChangeDocumentAndWaitAsync(new DidChangeTextDocumentParams {
        TextDocument = new OptionalVersionedTextDocumentIdentifier {
          Uri = documentItem.Uri,
          Version = documentItem.Version + 1
        },
        ContentChanges = new[] {
          new TextDocumentContentChangeEvent {
            Range = new Range((13, 0), (13, 1)),
            Text = ""
          }
        }
      }, CancellationTokenWithHighTimeout);

      // The initial document does not have issues. If the load was succesfully canceled, we should
      // receive diagnostics with a parser error.
      var report = await diagnosticReceiver.AwaitNextNotificationAsync(CancellationTokenWithHighTimeout);
      var diagnostics = report.Diagnostics.ToArray();
      Assert.AreEqual(1, diagnostics.Length);
    }

    [TestMethod, Timeout(MaxTestExecutionTimeMs)]
    public async Task VerificationErrorDetectedAfterCanceledSave() {
      // Create a document that'll be slightly slow to verify
      var source = @"
method Multiply(x: bv10, y: bv10) returns (product: bv10)
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
      var failSource = @"method Contradiction() { assert false; }";
      await SetUp(new Dictionary<string, string>() {
        { $"{DocumentOptions.Section}:{nameof(DocumentOptions.Verify)}", nameof(AutoVerification.OnSave) }
      });
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationTokenWithHighTimeout);

      DidChangeTextDocumentParams MakeChange(int? version, Range range, string text) {
        return new DidChangeTextDocumentParams {
          TextDocument = new OptionalVersionedTextDocumentIdentifier {
            Uri = documentItem.Uri,
            Version = version
          },
          ContentChanges = new[] {
            new TextDocumentContentChangeEvent {
              Range = range,
              Text = text
            }
          }
        };
      }

      // Add a space in the document
      var change1 = MakeChange(documentItem.Version + 1, new Range((0, 6), (0, 6)), " ");
      client.DidChangeTextDocument(change1);
      // Save and don't wait, so the next save will interrupt and cancel verification
      client.SaveDocument(documentItem);

      // Remove the space, and use a non-consecutive version to test that the server doesn't drop the change
      var change2 = MakeChange(documentItem.Version + 4, new Range((0, 6), (0, 7)), "");
      client.DidChangeTextDocument(change2);
      // Save and don't wait, so the next save will interrupt and cancel verification
      client.SaveDocument(documentItem);

      // Do the previous again a few times. This seems to be what it takes to guarantee cancelling verification.
      client.DidChangeTextDocument(MakeChange(documentItem.Version + 5, new Range((0, 6), (0, 6)), " "));
      client.SaveDocument(documentItem);
      client.DidChangeTextDocument(MakeChange(documentItem.Version + 6, new Range((0, 6), (0, 7)), ""));
      client.SaveDocument(documentItem);
      client.DidChangeTextDocument(MakeChange(documentItem.Version + 8, new Range((0, 6), (0, 6)), " "));
      client.SaveDocument(documentItem);
      client.DidChangeTextDocument(MakeChange(documentItem.Version + 9, new Range((0, 6), (0, 7)), ""));
      client.SaveDocument(documentItem);

      // Make a verification-breaking change, and use a non-consecutive version
      // to test that the server doesn't drop the change
      var change3 = MakeChange(documentItem.Version + 11, new Range((0, 0), (11, 1)), failSource);
      client.DidChangeTextDocument(change3);
      // Save and wait for the final result
      await client.SaveDocumentAndWaitAsync(documentItem, CancellationTokenWithHighTimeout);

      var document = await Documents.GetDocumentAsync(documentItem.Uri);
      Assert.IsNotNull(document);
      Assert.AreEqual(1, document.Errors.ErrorCount);
      Assert.AreEqual("assertion violation", document.Errors.GetDiagnostics(documentItem.Uri)[0].Message);
    }

    [TestMethod, Timeout(MaxTestExecutionTimeMs)]
    public async Task ChangeDocumentCancelsPreviousChange() {
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
      var initialLoadReport = await diagnosticReceiver.AwaitNextNotificationAsync(CancellationTokenWithHighTimeout);
      var initialLoadDiagnostics = initialLoadReport.Diagnostics.ToArray();
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

      await client.ChangeDocumentAndWaitAsync(new DidChangeTextDocumentParams {
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
      }, CancellationTokenWithHighTimeout);

      // The diagnostics of the initial document are already awaited. The original document contains a syntactic error.
      // The first change fixes the error. Therefore, if it was canceled by the second change, it should not report
      // any diagnostics.
      // The second change replaces the complete document with a correct one. Mind that the original document
      // was chosen because of the exceptionally long time it requires to verify.
      var report = await diagnosticReceiver.AwaitNextNotificationAsync(CancellationTokenWithHighTimeout);
      var diagnostics = report.Diagnostics.ToArray();
      Assert.AreEqual(0, diagnostics.Length);

      // This change is to ensure that no diagnostics are remaining in the report queue.
      var verificationDocumentItem = CreateTestDocument("class X {}", "verification.dfy");
      await client.OpenDocumentAndWaitAsync(verificationDocumentItem, CancellationTokenWithHighTimeout);
      var verificationReport = await diagnosticReceiver.AwaitNextNotificationAsync(CancellationTokenWithHighTimeout);
      Assert.AreEqual(verificationDocumentItem.Uri, verificationReport.Uri);
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
