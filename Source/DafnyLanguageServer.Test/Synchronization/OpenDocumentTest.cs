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
      (client, Server) = await Initialize(options => { }, modifyOptions);
    }

    [Fact]
    public async Task CorrectDocumentCanBeParsedResolvedAndVerifiedWithoutErrors() {
      var source = @"
function GetConstant(): int {
  1
}".Trim();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var document = await Projects.GetResolvedDocumentAsyncNormalizeUri(documentItem.Uri);
      Assert.NotNull(document);
      Assert.Empty(document.GetDiagnostics());
    }

    [Fact]
    public async Task ParseErrorsOfDocumentAreCaptured() {
      var source = @"
function GetConstant() int {
  1
}".Trim();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var document = await Projects.GetResolvedDocumentAsyncNormalizeUri(documentItem.Uri);
      Assert.NotNull(document);
      Assert.Single(document.GetDiagnostics());
      var message = document.GetDiagnostics()[documentItem.Uri.ToUri()].ElementAt(0);
      Assert.Equal(MessageSource.Parser.ToString(), message.Source);
    }

    [Fact]
    public async Task SemanticErrorsOfDocumentAreCaptured() {
      var source = @"
function GetConstant(): int {
  ""1""
}".Trim();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var document = await Projects.GetResolvedDocumentAsyncNormalizeUri(documentItem.Uri);
      Assert.NotNull(document);
      Assert.Single(document.GetDiagnostics());
      var message = document.GetDiagnostics()[documentItem.Uri.ToUri()].ElementAt(0);
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
      var documentItem = CreateTestDocument(source);
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
      await SetUp(options => options.Set(ServerCommand.Verification, VerifyOnMode.Never));
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var document = await Projects.GetResolvedDocumentAsyncNormalizeUri(documentItem.Uri);
      Assert.NotNull(document);
      Assert.True(document.GetDiagnostics()[documentItem.Uri.ToUri()].All(d => d.Severity != DiagnosticSeverity.Error));
    }

    [Fact]
    public async Task EmptyDocumentCanBeOpened() {
      var source = "";
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var document = await Projects.GetResolvedDocumentAsyncNormalizeUri(documentItem.Uri);
      Assert.NotNull(document);
      // Empty files currently yield only a warning.
      var diagnostics = document.GetDiagnostics();
      Assert.True(diagnostics[documentItem.Uri.ToUri()].All(d => d.Severity != DiagnosticSeverity.Error));
    }

    [Fact]
    public async Task DocumentWithNoValidTokensCanBeOpened() {
      var source = "";
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var document = await Projects.GetResolvedDocumentAsyncNormalizeUri(documentItem.Uri);
      Assert.NotNull(document);
      Assert.True(document.GetDiagnostics()[documentItem.Uri.ToUri()].All(d => d.Severity != DiagnosticSeverity.Error));
    }

    [Fact]
    public async Task EmptyDocumentCanBeIncluded() {
      var source = "include \"empty.dfy\"";
      var documentItem = CreateTestDocument(source, Path.Combine(Directory.GetCurrentDirectory(), "Synchronization/TestFiles/test.dfy"));
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var document = await Projects.GetResolvedDocumentAsyncNormalizeUri(documentItem.Uri);
      Assert.NotNull(document);
      Assert.False(document.GetDiagnostics().ContainsKey(documentItem.Uri.ToUri()));
    }

    public OpenDocumentTest(ITestOutputHelper output) : base(output) {
    }
  }
}
