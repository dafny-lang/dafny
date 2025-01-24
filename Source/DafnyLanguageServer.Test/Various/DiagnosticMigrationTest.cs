using System.Linq;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Dafny.LanguageServer.Workspace.ChangeProcessors;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Xunit;
using Xunit.Abstractions;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Various;

public class DiagnosticMigrationTest : ClientBasedLanguageServerTest {

  private const string FastToFailVerification = "function GetConstant(): int ensures false { 1 }";
  private const string FastToPassVerification = "function GetConstant2(): int { 1 }";

  [Fact]
  public async Task ResolutionDiagnosticsContainPreviousVerificationResultsWhenCodeIsInsertedAfter() {
    var documentItem = await CreateOpenAndWaitForResolve(FastToFailVerification, "untitled:Untitled-1");
    var verificationDiagnostics = await GetLastDiagnostics(documentItem);
    Assert.Single(verificationDiagnostics);
    ApplyChange(ref documentItem, new Range(0, 47, 0, 47), "\n\n" + NeverVerifies);
    var resolutionDiagnostics = await GetNextDiagnostics(documentItem);
    Assert.Equal(IdeState.OutdatedPrefix + verificationDiagnostics[0].Message, resolutionDiagnostics[0].Message);
  }

  [Fact]
  public async Task ResolutionDiagnosticsContainPreviousVerificationResultsWhenCodeIsInsertedBefore() {
    var documentItem = CreateTestDocument(FastToFailVerification, "ResolutionDiagnosticsContainPreviousVerificationResultsWhenCodeIsInsertedBefore.dfy");
    client.OpenDocument(documentItem);
    var verificationDiagnostics = await GetLastDiagnostics(documentItem);
    Assert.Single(verificationDiagnostics);
    ApplyChange(ref documentItem, new Range(0, 0, 0, 0), NeverVerifies + "\n\n");
    var resolutionDiagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken);
    Assert.Single(resolutionDiagnostics);
    // Verification diagnostic should have been moved.
    Assert.Equal(5, resolutionDiagnostics[0].Range.Start.Line);
    // Relation information should have been moved.
    Assert.Equal(5, resolutionDiagnostics[0].RelatedInformation!.ElementAt(0).Location.Range.Start.Line);
  }

  [Fact]
  public async Task ResolutionDiagnosticsAreRemovedWhenRangeIsDeleted() {
    var documentItem = CreateTestDocument(FastToFailVerification + "\n" + FastToPassVerification);
    client.OpenDocument(documentItem);
    var verificationDiagnostics = await GetLastDiagnostics(documentItem);
    Assert.Single(verificationDiagnostics);
    ApplyChange(ref documentItem, new Range(0, 0, 1, 0), "");
    var resolutionDiagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken);
    Assert.Empty(resolutionDiagnostics);
  }

  [Fact]
  public async Task ResolutionDiagnosticsAreKeptWhenNonEdgeCrossingChangesAreMade() {
    var documentItem = CreateTestDocument(@"method GetConstant() returns (x: int) 
  ensures x == 2 
  { 
    x := 1;
    return;
  }");
    client.OpenDocument(documentItem);
    var verificationDiagnostics = await GetLastDiagnostics(documentItem);
    Assert.Single(verificationDiagnostics);

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

    // NotificationPublisher.publishedDiagnostics is currently not migrated,
    // that's why the equality check fails and these parse diagnostics are sent.
    // Instead, there should be a single IDE state for the entire server, which is updated by a Compilation
    // https://github.com/dafny-lang/dafny/issues/4377
    var parseDiagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken);
    var resolutionDiagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken);
    Assert.Equal(verificationDiagnostics.Length, resolutionDiagnostics.Length);
    Assert.Equal(IdeState.OutdatedPrefix + verificationDiagnostics[0].Message, resolutionDiagnostics[0].Message);
    Assert.Equal(verificationDiagnostics[0].RelatedInformation, resolutionDiagnostics[0].RelatedInformation);
    Assert.Equal(new Range(4, 7, 4, 14), resolutionDiagnostics[0].Range);
  }

  [Fact]
  public async Task PassingANullChangeRangeClearsDiagnostics() {
    var documentItem = CreateTestDocument("method t() { var x: bool := 0; }");
    client.OpenDocument(documentItem);

    var resolutionDiagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken);
    Assert.Single(resolutionDiagnostics);

    ApplyChange(ref documentItem, null, "method u() ensures true { var x: bool := true; }");
    var verificationDiagnostics = await GetLastDiagnostics(documentItem);
    Assert.Empty(verificationDiagnostics);

    ApplyChange(ref documentItem, new Range(0, 42, 0, 46), "1");
    resolutionDiagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken);
    Assert.Single(resolutionDiagnostics);
  }

  [Fact]
  public async Task VerificationDiagnosticsCanBeMigratedAcrossMultipleResolutions() {
    var documentItem = CreateTestDocument(@"method GetConstant() returns (x: int) 
  ensures x == 2 
  { 
    x := 1;
    return;
  }");
    client.OpenDocument(documentItem);
    var verificationDiagnostics = await GetLastDiagnostics(documentItem);
    Assert.Single(verificationDiagnostics);

    ApplyChange(ref documentItem, new Range(0, 7, 0, 7), "{:neverVerify}");
    var resolutionDiagnostics1 = await GetNextDiagnostics(documentItem);
    Assert.Equal(IdeState.OutdatedPrefix + verificationDiagnostics[0].Message, resolutionDiagnostics1[0].Message);
    ApplyChange(ref documentItem, new Range(3, 9, 3, 10), "2");

    // Check that no other resolution diagnostics came in by fixing verification and getting new verification diagnostics.
    ApplyChange(ref documentItem, new Range(0, 7, 0, 21), "");
    var verificationDiagnostics2 = await GetLastDiagnostics(documentItem);
    Assert.Empty(verificationDiagnostics2);
  }

  [Fact]
  public async Task VerificationDiagnosticsDoNotShowUpTwice() {
    var documentItem = CreateTestDocument(@"method GetConstant() returns (x: int) 
  ensures x == 2 
  { 
    x := 1;
    return;
  }");
    client.OpenDocument(documentItem);
    var verificationDiagnostics = await GetLastDiagnostics(documentItem);
    Assert.Single(verificationDiagnostics);

    ApplyChange(ref documentItem, new Range(3, 9, 3, 10), "3");

    var resolutionDiagnostics = await GetNextDiagnostics(documentItem);
    Assert.Equal(IdeState.OutdatedPrefix + verificationDiagnostics[0].Message, resolutionDiagnostics[0].Message);
    var verificationDiagnostics2 = await GetLastDiagnostics(documentItem);
    Assert.Equal(verificationDiagnostics[0].Message, verificationDiagnostics2[0].Message);
    await AssertNoDiagnosticsAreComing(CancellationToken);
  }

  public DiagnosticMigrationTest(ITestOutputHelper output) : base(output) {
  }
}
