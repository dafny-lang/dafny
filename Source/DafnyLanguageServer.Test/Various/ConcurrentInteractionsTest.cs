using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Microsoft.Dafny.LanguageServer.Workspace;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using OmniSharp.Extensions.JsonRpc.Server;
using Xunit;
using Xunit.Abstractions;
using XunitAssertMessages;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Various {

  [Collection("Sequential Collection")]
  public class ConcurrentInteractionsTest : ClientBasedLanguageServerTest {
    // Implementation note: These tests assume that no diagnostics are published
    // when a document (re-load) was canceled.
    private const int MaxTestExecutionTimeMs = 240_000;

    [Fact]
    public async Task UpdateDuringARequestWillCancelTheRequest() {
      var programThatResolvesSlowlyEnough = RepeatStrBuilder(@"method Foo() {}", 1000);
      var documentItem = CreateTestDocument(programThatResolvesSlowlyEnough, "UpdateDuringARequestWillCancelTheRequest.dfy");
      client.OpenDocument(documentItem);
      var hoverTask = client.RequestHover(new HoverParams { Position = (0, 0), TextDocument = documentItem }, CancellationToken);
      ApplyChange(ref documentItem, new Range(0, 0, 0, 0), "//comment\n");
#pragma warning disable VSTHRD003
      await Assert.ThrowsAsync<ContentModifiedException>(() => hoverTask);
#pragma warning restore VSTHRD003
    }

    private static string RepeatStrBuilder(string text, uint n) {
      return new StringBuilder(text.Length * (int)n)
        .Insert(0, text, (int)n)
        .ToString();
    }

    [Fact(Timeout = MaxTestExecutionTimeMs)]
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
      await SetUp(options => options.Set(ProjectManager.Verification, VerifyOnMode.Save));
      var documentItem = CreateTestDocument(source, "VerificationErrorDetectedAfterCanceledSave.dfy");
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
      ApplyChange(ref documentItem, new Range((0, 6), (0, 6)), " ");
      // Save and don't wait, so the next save will interrupt and cancel verification
      client.SaveDocument(documentItem);

      // Remove the space, and use a non-consecutive version to test that the server doesn't drop the change
      var change2 = MakeChange(documentItem.Version + 2, new Range((0, 6), (0, 7)), "");
      documentItem = documentItem with { Version = change2.TextDocument.Version };
      client.DidChangeTextDocument(change2);
      // Save and don't wait, so the next save will interrupt and cancel verification
      client.SaveDocument(documentItem);

      // Do the previous again a few times. This seems to be what it takes to guarantee cancelling verification.
      ApplyChange(ref documentItem, new Range((0, 6), (0, 7)), " ");
      client.SaveDocument(documentItem);
      ApplyChange(ref documentItem, new Range((0, 6), (0, 7)), "");
      client.SaveDocument(documentItem);
      ApplyChange(ref documentItem, new Range((0, 6), (0, 7)), " ");
      client.SaveDocument(documentItem);
      ApplyChange(ref documentItem, new Range((0, 6), (0, 7)), "");
      client.SaveDocument(documentItem);

      // Make a verification-breaking change, and use a non-consecutive version
      // to test that the server doesn't drop the change
      var change3 = MakeChange(documentItem.Version + 2, new Range((0, 0), (11, 1)), failSource);
      documentItem = documentItem with { Version = change3.TextDocument.Version };
      client.DidChangeTextDocument(change3);
      // Save and wait for the final result
      await client.SaveDocumentAndWaitAsync(documentItem, CancellationTokenWithHighTimeout);

      var diagnostics = await GetLatestDiagnosticsParams(documentItem, CancellationToken);
      Assert.Equal(documentItem.Version, diagnostics.Version);
      Assert.Single(diagnostics.Diagnostics);
      AssertM.Equal("assertion could not be proved", diagnostics.Diagnostics.First().Message, "actual diagnostic message was: " + diagnostics.Diagnostics.First().Message);
    }

    [Fact]
    public async Task ChangeDocumentCancelsPreviousOpenAndChangeVerification() {
      var source = NeverVerifies.Substring(0, NeverVerifies.Length - 2);
      var documentItem = CreateTestDocument(source, "ChangeDocumentCancelsPreviousOpenAndChangeVerification.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationTokenWithHighTimeout);
      // The original document contains a syntactic error.
      var initialLoadDiagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationTokenWithHighTimeout, documentItem);
      await AssertNoDiagnosticsAreComing(CancellationTokenWithHighTimeout);
      Assert.Single(initialLoadDiagnostics);

      ApplyChange(ref documentItem, new Range((2, 1), (2, 1)), "\n}");

      // Wait for parse diagnostics now, so they don't get cancelled.
      // After this we still have never completing verification diagnostics in the queue.
      var parseErrorFixedDiagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationTokenWithHighTimeout, documentItem);
      Assert.Empty(parseErrorFixedDiagnostics);

      // Cancel the slow verification and start a fast verification
      ApplyChange(ref documentItem, new Range((0, 0), (3, 1)), "function GetConstant(): int ensures false { 1 }");

      var verificationDiagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationTokenWithHighTimeout, documentItem);
      Assert.Single(verificationDiagnostics);

      await AssertNoDiagnosticsAreComing(CancellationTokenWithHighTimeout);
    }

    /// <summary>
    /// If this test is flaky, increase the amount of lines in the source program
    /// </summary>
    [Fact(Timeout = MaxTestExecutionTimeMs, Skip = "Not working")]
    public async Task ChangeDocumentCancelsPreviousResolution() {
      string CreateCorrectFunction(int index) => @$"function GetConstant{index}(x: int): int {{ x }}";

      var functionWithResolutionError = "function GetConstant(): int { x }\n";
      var slowToResolveSource = functionWithResolutionError + string.Join("\n", Enumerable.Range(0, 1000).Select(CreateCorrectFunction));
      var documentItem = CreateTestDocument(slowToResolveSource, "veryLongDocument.dfy");
      client.OpenDocument(documentItem);

      // Change but keep a resolution error, cancel previous diagnostics
      ApplyChange(ref documentItem, new Range((0, 30), (0, 31)), "y");

      // Fix resolution error, cancel previous diagnostics
      ApplyChange(ref documentItem, new Range((0, 30), (0, 31)), "1");

      var resolutionDiagnostics = await GetNextDiagnostics(documentItem);
      Assert.Empty(resolutionDiagnostics);

      var verificationDiagnostics = await GetNextDiagnostics(documentItem);
      Assert.Empty(verificationDiagnostics);

      await AssertNoDiagnosticsAreComing(CancellationToken);
    }

    [Fact]
    public async Task CanLoadMultipleDocumentsConcurrently() {
      // The current implementation of DafnyLangParser, DafnyLangSymbolResolver, and DafnyProgramVerifier are only mutual
      // exclusive to themselves. This "stress test" ensures that loading multiple documents at once is possible.
      // To be more specific, this test should ensure that there is no state discarded/overriden between the three steps within
      // the Dafny Compiler itself.
      int documentsToLoadConcurrently = 50;
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
        var documentItem = CreateTestDocument(source, $"current_test_{i}.dfy");
        client.OpenDocument(documentItem);
        loadingDocuments.Add(documentItem);
      }
      for (int i = 0; i < documentsToLoadConcurrently; i++) {
        await client.WaitForNotificationCompletionAsync(loadingDocuments[i].Uri, CancellationTokenWithHighTimeout);
      }

      foreach (var loadingDocument in loadingDocuments) {
        client.CloseDocument(loadingDocument);
      }
      await AssertNoDiagnosticsAreComing(CancellationTokenWithHighTimeout);
    }

    public ConcurrentInteractionsTest(ITestOutputHelper output) : base(output) {
    }
  }
}
