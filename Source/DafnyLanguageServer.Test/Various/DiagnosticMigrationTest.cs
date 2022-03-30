using System.Linq;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using OmniSharp.Extensions.LanguageServer.Protocol.Client;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Various;

[TestClass]
public class DiagnosticMigrationTest : ClientBasedLanguageServerTest {

  private const string FastToFailVerification = "function GetConstant(): int ensures false { 1 }";
  private const string FastToPassVerification = "function GetConstant2(): int { 1 }";

  [TestMethod]
  public async Task ResolutionDiagnosticsContainPreviousVerificationResultsWhenCodeIsInsertedAfter() {
    var documentItem = CreateTestDocument(FastToFailVerification);
    client.OpenDocument(documentItem);
    var verificationDiagnostics = await diagnosticReceiver.AwaitVerificationDiagnosticsAsync(CancellationToken);
    Assert.AreEqual(1, verificationDiagnostics.Length);
    ApplyChange(ref documentItem, new Range(0, 47, 0, 47), "\n\n" + NeverVerifies);
    var resolutionDiagnostics = await diagnosticReceiver.AwaitNextDiagnosticsAsync(CancellationToken);
    Assert.AreEqual(verificationDiagnostics[0], resolutionDiagnostics[0]);
  }

  [TestMethod]
  public async Task ResolutionDiagnosticsContainPreviousVerificationResultsWhenCodeIsInsertedBefore() {
    var documentItem = CreateTestDocument(FastToFailVerification);
    client.OpenDocument(documentItem);
    var verificationDiagnostics = await diagnosticReceiver.AwaitVerificationDiagnosticsAsync(CancellationToken);
    Assert.AreEqual(1, verificationDiagnostics.Length);
    ApplyChange(ref documentItem, new Range(0, 0, 0, 0), NeverVerifies + "\n\n");
    var resolutionDiagnostics = await diagnosticReceiver.AwaitNextDiagnosticsAsync(CancellationToken);
    Assert.AreEqual(1, resolutionDiagnostics.Length);
    // Verification diagnostic should have been moved.
    Assert.AreEqual(5, resolutionDiagnostics[0].Range.Start.Line);
    // Relation information should have been moved.
    Assert.AreEqual(5, resolutionDiagnostics[0].RelatedInformation!.ElementAt(0).Location.Range.Start.Line);
  }

  [TestMethod]
  public async Task ResolutionDiagnosticsAreRemovedWhenRangeIsDeleted() {
    var documentItem = CreateTestDocument(FastToFailVerification + "\n" + FastToPassVerification);
    client.OpenDocument(documentItem);
    var verificationDiagnostics = await diagnosticReceiver.AwaitVerificationDiagnosticsAsync(CancellationToken);
    Assert.AreEqual(1, verificationDiagnostics.Length);
    ApplyChange(ref documentItem, new Range(0, 0, 1, 0), "");
    var resolutionDiagnostics = await diagnosticReceiver.AwaitNextDiagnosticsAsync(CancellationToken);
    Assert.AreEqual(0, resolutionDiagnostics.Length);
  }

  [TestMethod]
  public async Task ResolutionDiagnosticsAreKeptWhenNonEdgeCrossingChangesAreMade() {
    var documentItem = CreateTestDocument(@"method GetConstant() returns (x: int) 
  ensures x == 2 
  { 
    x := 1;
    return;
  }");
    client.OpenDocument(documentItem);
    var verificationDiagnostics = await diagnosticReceiver.AwaitVerificationDiagnosticsAsync(CancellationToken);
    Assert.AreEqual(1, verificationDiagnostics.Length);

    client.DidChangeTextDocument(new DidChangeTextDocumentParams {
      TextDocument = new OptionalVersionedTextDocumentIdentifier {
        Uri = documentItem.Uri,
        Version = documentItem.Version + 1
      },
      ContentChanges = new[] {
        new TextDocumentContentChangeEvent {
          Range = new Range(1, 12, 1, 13),
          Text = "!"
        },

        new TextDocumentContentChangeEvent {
          Range = new Range(4, 4, 4, 10),
          Text = "tempReturn"
        },

        new TextDocumentContentChangeEvent {
          Range = new Range(4, 4, 4, 14),
          Text = "return"
        },

        new TextDocumentContentChangeEvent {
          Range = new Range(4, 4, 4, 4),
          Text = "   "
        }
      }
    });

    var resolutionDiagnostics = await diagnosticReceiver.AwaitNextDiagnosticsAsync(CancellationToken);
    Assert.AreEqual(verificationDiagnostics.Length, resolutionDiagnostics.Length);
    Assert.AreEqual(verificationDiagnostics[0].Message, resolutionDiagnostics[0].Message);
    Assert.AreEqual(verificationDiagnostics[0].RelatedInformation, resolutionDiagnostics[0].RelatedInformation);
    Assert.AreEqual(new Range(4, 7, 4, 13), resolutionDiagnostics[0].Range);
  }

  [TestMethod]
  public async Task PassingANullChangeRangeClearsDiagnostics() {
    var documentItem = CreateTestDocument("method t() { var x: bool := 0; }");
    client.OpenDocument(documentItem);

    var resolutionDiagnostics = await diagnosticReceiver.AwaitNextDiagnosticsAsync(CancellationToken);
    Assert.AreEqual(1, resolutionDiagnostics.Length);

    ApplyChange(ref documentItem, null, "method u() { var x: bool := true; }");
    resolutionDiagnostics = await diagnosticReceiver.AwaitNextDiagnosticsAsync(CancellationToken);
    var verificationDiagnostics = await diagnosticReceiver.AwaitNextDiagnosticsAsync(CancellationToken);
    Assert.AreEqual(0, resolutionDiagnostics.Length);
    Assert.AreEqual(0, verificationDiagnostics.Length);

    ApplyChange(ref documentItem, new Range(0, 28, 0, 32), "1");
    resolutionDiagnostics = await diagnosticReceiver.AwaitNextDiagnosticsAsync(CancellationToken);
    Assert.AreEqual(1, resolutionDiagnostics.Length);
  }

  [TestMethod]
  public async Task VerificationDiagnosticsCanBeMigratedAcrossMultipleResolutions() {
    var documentItem = CreateTestDocument(@"method GetConstant() returns (x: int) 
  ensures x == 2 
  { 
    x := 1;
    return;
  }");
    client.OpenDocument(documentItem);
    var verificationDiagnostics = await diagnosticReceiver.AwaitVerificationDiagnosticsAsync(CancellationToken);
    Assert.AreEqual(1, verificationDiagnostics.Length);

    ApplyChange(ref documentItem, new Range(0, 7, 0, 7), "{:neverVerify}");
    var resolutionDiagnostics1 = await diagnosticReceiver.AwaitNextDiagnosticsAsync(CancellationToken);
    ApplyChange(ref documentItem, new Range(3, 9, 3, 10), "2");
    var resolutionDiagnostics2 = await diagnosticReceiver.AwaitNextDiagnosticsAsync(CancellationToken);

    Assert.AreEqual(1, resolutionDiagnostics1.Length);
    Assert.AreEqual(1, resolutionDiagnostics2.Length);
    Assert.AreEqual(resolutionDiagnostics1[0], resolutionDiagnostics2[0]);
  }

  [TestMethod]
  public async Task VerificationDiagnosticsDoNotShowUpTwice() {
    var documentItem = CreateTestDocument(@"method GetConstant() returns (x: int) 
  ensures x == 2 
  { 
    x := 1;
    return;
  }");
    client.OpenDocument(documentItem);
    var verificationDiagnostics1 = await diagnosticReceiver.AwaitVerificationDiagnosticsAsync(CancellationToken);
    Assert.AreEqual(1, verificationDiagnostics1.Length);

    ApplyChange(ref documentItem, new Range(3, 9, 3, 10), "3");
    var verificationDiagnostics2 = await diagnosticReceiver.AwaitVerificationDiagnosticsAsync(CancellationToken);

    Assert.AreEqual(verificationDiagnostics1.Length, verificationDiagnostics2.Length);
    Assert.AreEqual(verificationDiagnostics1[0], verificationDiagnostics2[0]);
  }
}