using System;
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
using Microsoft.CodeAnalysis.Operations;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Various {
  [TestClass]
  public class ConcurrentInteractionsTest : ClientBasedLanguageServerTest {
    // Implementation note: These tests assume that no diagnostics are published
    // when a document (re-load) was canceled (DafnyDocument.LoadCanceled).
    private const int MaxTestExecutionTimeMs = 240_000;
    private const int MaxRequestExecutionTimeMs = 180_000;

    // We do not use the LanguageServerTestBase.cancellationToken here because it has a timeout.
    // Since these tests are slow, we do not use the timeout here.
    private CancellationTokenSource cancellationSource;

    private CancellationToken CancellationTokenWithHighTimeout => cancellationSource.Token;

    [TestInitialize]
    public override async Task SetUp() {
      await base.SetUp();
      cancellationSource = new();
      cancellationSource.CancelAfter(MaxRequestExecutionTimeMs);
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
      Assert.IsFalse(await DidMoreDiagnosticsCome());
      Assert.AreEqual(1, initialLoadDiagnostics.Length);

      ApplyChange(ref documentItem, new Range((12, 3), (12, 3)), "\n}");

      // Wait for resolution diagnostics now, so they don't get cancelled.
      // After this we still have slow verification diagnostics in the queue.
      var parseErrorFixedDiagnostics = await diagnosticReceiver.AwaitNextDiagnosticsAsync(CancellationTokenWithHighTimeout);
      Assert.AreEqual(0, parseErrorFixedDiagnostics.Length);

      // Cancel the slow verification and start a fast verification
      ApplyChange(ref documentItem, new Range((0, 0), (13, 1)), "function GetConstant(): int ensures false { 1 }");

      var parseErrorStillFixedDiagnostics = await diagnosticReceiver.AwaitNextDiagnosticsAsync(CancellationTokenWithHighTimeout);
      Assert.AreEqual(0, parseErrorStillFixedDiagnostics.Length);

      var verificationDiagnostics = await diagnosticReceiver.AwaitNextDiagnosticsAsync(CancellationTokenWithHighTimeout);
      Assert.AreEqual(1, verificationDiagnostics.Length);

      Assert.IsFalse(await DidMoreDiagnosticsCome());
    }

    /// <summary>
    /// If this test is flaky, increase the amount of lines in the source program
    /// </summary>
    // [TestMethod, Timeout(MaxTestExecutionTimeMs)]
    public async Task ChangeDocumentCancelsPreviousResolution() {
      string CreateCorrectFunction(int index) => @$"function GetConstant{index}(x: int): int {{ x }}";
      
      var functionWithResolutionError = "function GetConstant(): int { x }\n";
      var slowToResolveSource = functionWithResolutionError + string.Join("\n", Enumerable.Range(0, 1000).Select(CreateCorrectFunction));
      var documentItem = CreateTestDocument(slowToResolveSource);
      client.OpenDocument(documentItem);

      // Change but keep a resolution error, cancel previous diagnostics
      ApplyChange(ref documentItem, new Range((0, 30), (0, 31)), "y");

      // Fix resolution error, cancel previous diagnostics
      ApplyChange(ref documentItem, new Range((0, 30), (0, 31)), "1");

      var resolutionDiagnostics = await diagnosticReceiver.AwaitNextDiagnosticsAsync(CancellationToken);
      Assert.AreEqual(0, resolutionDiagnostics.Length);

      var verificationDiagnostics = await diagnosticReceiver.AwaitNextDiagnosticsAsync(CancellationToken);
      Assert.AreEqual(0, verificationDiagnostics.Length);

      Assert.IsFalse(await DidMoreDiagnosticsCome());
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
        var report = await diagnosticReceiver.AwaitVerificationDiagnosticsAsync(CancellationTokenWithHighTimeout);
        Assert.AreEqual(0, report.Length);
      }
      Assert.IsFalse(await DidMoreDiagnosticsCome());
    }
  }
}
