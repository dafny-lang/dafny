using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.Workspace;
using System.Linq;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Xunit;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Synchronization {
  public class SaveDocumentTest : ClientBasedLanguageServerTest {

    [Fact]
    public async Task LeavesDocumentUnchangedIfVerifyOnChange() {
      var source = @"
function GetConstant(): int {
  1
}".Trim();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await GetLastDiagnostics(documentItem, CancellationToken);
      await client.SaveDocumentAndWaitAsync(documentItem, CancellationToken);
      await AssertNoDiagnosticsAreComing(CancellationToken);
    }

    [Fact]
    public async Task LeavesDocumentUnchangedIfVerifyNever() {
      var source = @"
function GetConstant(): int {
  1
}".Trim();
      await SetUp(options => options.Set(ServerCommand.Verification, VerifyOnMode.Never));
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await GetLastDiagnostics(documentItem, CancellationToken);
      await client.SaveDocumentAndWaitAsync(documentItem, CancellationToken);
      await AssertNoDiagnosticsAreComing(CancellationToken);
    }

    [Fact]
    public async Task LeavesDocumentUnchangedIfDocumentContainsSyntaxErrorsIfVerifyOnSave() {
      var source = @"
function GetConstant() int {
  1
}".Trim();
      await SetUp(options => options.Set(ServerCommand.Verification, VerifyOnMode.Save));
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await GetLastDiagnostics(documentItem, CancellationToken);
      await client.SaveDocumentAndWaitAsync(documentItem, CancellationToken);
      await AssertNoDiagnosticsAreComing(CancellationToken);
    }

    [Fact]
    public async Task LeavesDocumentUnchangedIfDocumentContainsSemanticErrorsIfVerifyOnSave() {
      var source = @"
function GetConstant(): int {
  d
}".Trim();
      await SetUp(options => options.Set(ServerCommand.Verification, VerifyOnMode.Save));
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await GetLastDiagnostics(documentItem, CancellationToken);
      await client.SaveDocumentAndWaitAsync(documentItem, CancellationToken);
      await AssertNoDiagnosticsAreComing(CancellationToken);
    }

    [Fact]
    public async Task UpdatesFlawlessDocumentIfVerifyOnSave() {
      var source = @"
function GetConstant(): int {
  1
}".Trim();
      await SetUp(options => options.Set(ServerCommand.Verification, VerifyOnMode.Save));
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await GetLastDiagnostics(documentItem, CancellationToken);
      await client.SaveDocumentAndWaitAsync(documentItem, CancellationToken);
      await AssertNoDiagnosticsAreComing(CancellationToken);
    }

    [Fact]
    public async Task VerificationErrorsAreCapturedIfVerifyOnSave() {
      var source = @"
method DoIt() {
  assert false;
}".Trim();
      await SetUp(options => options.Set(ServerCommand.Verification, VerifyOnMode.Save));
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await GetLastDiagnostics(documentItem, CancellationToken);
      await client.SaveDocumentAndWaitAsync(documentItem, CancellationToken);
      var afterSaveDiagnostics = await GetLastDiagnostics(documentItem, CancellationToken);
      Assert.Single(afterSaveDiagnostics);
      var message = afterSaveDiagnostics.First();
      Assert.Equal(MessageSource.Verifier.ToString(), message.Source);
    }
  }
}
