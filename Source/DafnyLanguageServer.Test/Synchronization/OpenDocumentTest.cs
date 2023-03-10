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
      client = await InitializeClient(options => { }, modifyOptions);
    }

    [Fact]
    public async Task CorrectDocumentCanBeParsedResolvedAndVerifiedWithoutErrors() {
      var source = @"
function GetConstant(): int {
  1
}".Trim();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var document = await Documents.GetResolvedDocumentAsync(documentItem.Uri);
      Assert.NotNull(document);
      Assert.Empty(document.Diagnostics);
    }

    [Fact]
    public async Task ParseErrorsOfDocumentAreCaptured() {
      var source = @"
function GetConstant() int {
  1
}".Trim();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var document = await Documents.GetResolvedDocumentAsync(documentItem.Uri);
      Assert.NotNull(document);
      Assert.Single(document.Diagnostics);
      var message = document.Diagnostics.ElementAt(0);
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
      var document = await Documents.GetResolvedDocumentAsync(documentItem.Uri);
      Assert.NotNull(document);
      Assert.Single(document.Diagnostics);
      var message = document.Diagnostics.ElementAt(0);
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
      var document = await Documents.GetLastDocumentAsync(documentItem.Uri);
      Assert.NotNull(document);
      Assert.Equal(1, document.Diagnostics.Count(d => d.Severity == DiagnosticSeverity.Error));
      var message = document.Diagnostics.First(d => d.Severity!.Value == DiagnosticSeverity.Error);
      Assert.Equal(MessageSource.Verifier.ToString(), message.Source);
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
      var document = await Documents.GetResolvedDocumentAsync(documentItem.Uri);
      Assert.NotNull(document);
      Assert.True(!document.Diagnostics.Any(d => d.Severity == DiagnosticSeverity.Error));
    }

    [Fact]
    public async Task EmptyDocumentCanBeOpened() {
      var source = "";
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var document = await Documents.GetResolvedDocumentAsync(documentItem.Uri);
      Assert.NotNull(document);
      // Empty files currently yield only a warning.
      Assert.True(document.Diagnostics.All(d => d.Severity != DiagnosticSeverity.Error));
    }

    [Fact]
    public async Task DocumentWithNoValidTokensCanBeOpened() {
      var source = "";
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var document = await Documents.GetResolvedDocumentAsync(documentItem.Uri);
      Assert.NotNull(document);
      Assert.True(document.Diagnostics.All(d => d.Severity != DiagnosticSeverity.Error));
    }

    [Fact]
    public async Task EmptyDocumentCanBeIncluded() {
      var source = "include \"empty.dfy\"";
      var documentItem = CreateTestDocument(source, Path.Combine(Directory.GetCurrentDirectory(), "Synchronization/TestFiles/test.dfy"));
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var document = await Documents.GetResolvedDocumentAsync(documentItem.Uri);
      Assert.NotNull(document);
      Assert.True(!document.Diagnostics.Any());
    }

    public OpenDocumentTest(ITestOutputHelper output) : base(output) {
    }
  }
}
