using System;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.Workspace;
using OmniSharp.Extensions.LanguageServer.Protocol.Client;
using System.Linq;
using System.Threading.Tasks;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.IO;
using Xunit.Abstractions;
using Xunit;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Synchronization {

  public class OpenDocumentTest : DafnyLanguageServerTestBase, IAsyncLifetime {
    private ILanguageClient client;

    public async Task InitializeAsync() {
      await SetUp(null);
    }

    public Task DisposeAsync() {
      return Task.CompletedTask;
    }

    private async Task SetUp(Action<DafnyOptions> modifyOptions) {
      (client, Server) = await Initialize(_ => { }, modifyOptions);
    }

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
      Assert.Single(document.GetDiagnosticUris());
      var message = document.GetDiagnosticsForUri(documentItem.Uri.ToUri()).ElementAt(0);
      Assert.Equal(MessageSource.Parser.ToString(), message.Source);
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
      Assert.Single(document.GetDiagnosticUris());
      var message = document.GetDiagnosticsForUri(documentItem.Uri.ToUri()).ElementAt(0);
      Assert.Equal(MessageSource.Resolver.ToString(), message.Source);
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
      var document = await Projects.GetLastDocumentAsync(documentItem.Uri);
      Assert.NotNull(document);
      var dafnyDiagnostics = document.GetDiagnostics(documentItem.Uri.ToUri()).ToList();
      Assert.Equal(1, dafnyDiagnostics.Count(d => d.Level == ErrorLevel.Error));
      var message = dafnyDiagnostics.First(d => d.Level == ErrorLevel.Error);
      Assert.Equal(MessageSource.Verifier, message.Source);
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
      var document = await Projects.GetResolvedDocumentAsyncNormalizeUri(documentItem.Uri);
      Assert.NotNull(document);
      Assert.True(document.GetDiagnosticsForUri(documentItem.Uri.ToUri()).All(d => d.Severity != DiagnosticSeverity.Error));
    }

    [Fact]
    public async Task EmptyDocumentCanBeOpened() {
      var source = "";
      var documentItem = CreateTestDocument(source, "EmptyDocumentCanBeOpened.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var document = await Projects.GetResolvedDocumentAsyncNormalizeUri(documentItem.Uri);
      Assert.NotNull(document);
      // Empty files currently yield only a warning.
      Assert.True(document.GetDiagnosticsForUri(documentItem.Uri.ToUri()).All(d => d.Severity != DiagnosticSeverity.Error));
    }

    [Fact]
    public async Task DocumentWithNoValidTokensCanBeOpened() {
      var source = "";
      var documentItem = CreateTestDocument(source, "DocumentWithNoValidTokensCanBeOpened.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var document = await Projects.GetResolvedDocumentAsyncNormalizeUri(documentItem.Uri);
      Assert.NotNull(document);
      Assert.True(document.GetDiagnosticsForUri(documentItem.Uri.ToUri()).All(d => d.Severity != DiagnosticSeverity.Error));
    }

    [Fact]
    public async Task EmptyDocumentCanBeIncluded() {
      var source = "include \"empty.dfy\"";
      var documentItem = CreateTestDocument(source, Path.Combine(Directory.GetCurrentDirectory(), "Synchronization/TestFiles/test.dfy"));
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var document = await Projects.GetResolvedDocumentAsyncNormalizeUri(documentItem.Uri);
      Assert.NotNull(document);
      Assert.DoesNotContain(documentItem.Uri.ToUri(), document.GetDiagnosticUris());
    }

    public OpenDocumentTest(ITestOutputHelper output) : base(output) {
    }
  }
}
