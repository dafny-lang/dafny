using System;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.Workspace;
using OmniSharp.Extensions.LanguageServer.Protocol.Client;
using System.Linq;
using System.Threading.Tasks;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.IO;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Xunit.Abstractions;
using Xunit;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Synchronization {

  public class OpenDocumentTest : ClientBasedLanguageServerTest {

    [Fact]
    public async Task CorrectDocumentCanBeParsedResolvedAndVerifiedWithoutErrors() {
      var source = @"
function GetConstant(): int {
  1
}".Trim();
      var documentItem = CreateTestDocument(source, "CorrectDocumentCanBeParsedResolvedAndVerifiedWithoutErrors.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var state = await Projects.GetResolvedDocumentAsyncNormalizeUri(documentItem.Uri);
      Assert.NotNull(state);
      Assert.Empty(state.GetAllDiagnostics());
    }

    [Fact]
    public async Task ParseErrorsOfDocumentAreCaptured() {
      var source = @"
function GetConstant() int {
  1
}".Trim();
      var documentItem = CreateTestDocument(source, "ParseErrorsOfDocumentAreCaptured.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var document = await Projects.GetParsedDocumentNormalizeUri(documentItem.Uri);
      Assert.NotNull(document);
      var diagnostics = await GetLastDiagnostics(documentItem);
      Assert.Single(diagnostics);
      Assert.Equal(MessageSource.Parser.ToString(), diagnostics[0].Source);
    }

    [Fact]
    public async Task SemanticErrorsOfDocumentAreCaptured() {
      var source = @"
function GetConstant(): int {
  ""1""
}".Trim();
      var documentItem = CreateTestDocument(source, "SemanticErrorsOfDocumentAreCaptured.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var document = await Projects.GetResolvedDocumentAsyncNormalizeUri(documentItem.Uri);
      Assert.NotNull(document);
      var diagnostics = await GetLastDiagnostics(documentItem);
      Assert.Single(diagnostics);
      Assert.Equal(MessageSource.Resolver.ToString(), diagnostics[0].Source);
    }

    [Fact]
    public async Task VerificationErrorsOfDocumentAreCaptured() {
      var source = @"
method Recurse(x: int) returns (r: int) {
    if(x == 0) {
        r := 0;
    } else {
        r := Recurse(x - 1);
    }
}".Trim();
      var documentItem = CreateTestDocument(source, "VerificationErrorsOfDocumentAreCaptured.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var diagnostics = await GetLastDiagnostics(documentItem, DiagnosticSeverity.Error);
      Assert.Single(diagnostics);
      Assert.Equal(MessageSource.Verifier.ToString(), diagnostics.First().Source);
    }

    [Fact]
    public async Task VerificationErrorsOfDocumentAreNotCapturedIfAutoVerificationIsNotOnChange() {

      var source = @"
method Recurse(x: int) returns (r: int) {
    if(x == 0) {
        r := 0;
    } else {
        r := Recurse(x - 1);
    }
}".Trim();
      await SetUp(options => options.Set(ProjectManager.Verification, VerifyOnMode.Never));
      var documentItem = CreateTestDocument(source, "VerificationErrorsOfDocumentAreNotCapturedIfAutoVerificationIsNotOnChange.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await AssertNoDiagnosticsAreComing(CancellationToken, documentItem);
    }

    [Fact]
    public async Task EmptyDocumentCanBeOpened() {
      var source = "";
      var documentItem = CreateTestDocument(source, "EmptyDocumentCanBeOpened.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var document = await Projects.GetResolvedDocumentAsyncNormalizeUri(documentItem.Uri);
      Assert.NotNull(document);
    }

    [Fact]
    public async Task DocumentWithNoValidTokensCanBeOpened() {
      var source = "";
      var documentItem = CreateTestDocument(source, "DocumentWithNoValidTokensCanBeOpened.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var document = await Projects.GetResolvedDocumentAsyncNormalizeUri(documentItem.Uri);
      Assert.NotNull(document);
    }

    [Fact]
    public async Task EmptyDocumentCanBeIncluded() {
      var source = "include \"empty.dfy\"";
      var documentItem = CreateTestDocument(source, Path.Combine(Directory.GetCurrentDirectory(), "Synchronization/TestFiles/test.dfy"));
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await AssertNoDiagnosticsAreComing(CancellationToken, forDocument: documentItem);
    }

    public OpenDocumentTest(ITestOutputHelper output) : base(output) {
    }
  }
}
