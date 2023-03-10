using System;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using OmniSharp.Extensions.LanguageServer.Protocol.Client;
using System.Linq;
using System.Threading.Tasks;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.IO;
using Microsoft.Extensions.DependencyInjection;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Synchronization {

  [TestClass]
  public class OpenDocumentTest : DafnyLanguageServerTestBase {
    private ILanguageClient client;

    [TestInitialize]
    public Task SetUp() => SetUp(null);

    public async Task SetUp(Action<DafnyOptions> modifyOptions) {
      client = await InitializeClient(options => {
      }, modifyOptions);
    }

    [TestMethod]
    public async Task CorrectDocumentCanBeParsedResolvedAndVerifiedWithoutErrors() {
      var source = @"
function GetConstant(): int {
  1
}".Trim();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var document = await Documents.GetResolvedDocumentAsync(documentItem.Uri);
      Assert.IsNotNull(document);
      Assert.AreEqual(0, document.Diagnostics.Count());
    }

    [TestMethod]
    public async Task ParseErrorsOfDocumentAreCaptured() {
      var source = @"
function GetConstant() int {
  1
}".Trim();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var document = await Documents.GetResolvedDocumentAsync(documentItem.Uri);
      Assert.IsNotNull(document);
      Assert.AreEqual(1, document.Diagnostics.Count());
      var message = document.Diagnostics.ElementAt(0);
      Assert.AreEqual(MessageSource.Parser.ToString(), message.Source);
    }

    [TestMethod]
    public async Task SemanticErrorsOfDocumentAreCaptured() {
      var source = @"
function GetConstant(): int {
  ""1""
}".Trim();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var document = await Documents.GetResolvedDocumentAsync(documentItem.Uri);
      Assert.IsNotNull(document);
      Assert.AreEqual(1, document.Diagnostics.Count());
      var message = document.Diagnostics.ElementAt(0);
      Assert.AreEqual(MessageSource.Resolver.ToString(), message.Source);
    }

    [TestMethod]
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
      Assert.IsNotNull(document);
      Assert.AreEqual(1, document.Diagnostics.Count(d => d.Level == ErrorLevel.Error));
      var message = document.Diagnostics.First(d => d.Level == ErrorLevel.Error);
      Assert.AreEqual(MessageSource.Verifier, message.Source);
    }

    [TestMethod]
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
      Assert.IsNotNull(document);
      Assert.IsTrue(!document.Diagnostics.Any(d => d.Severity == DiagnosticSeverity.Error));
    }

    [TestMethod]
    public async Task EmptyDocumentCanBeOpened() {
      var source = "";
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var document = await Documents.GetResolvedDocumentAsync(documentItem.Uri);
      Assert.IsNotNull(document);
      // Empty files currently yield only a warning.
      Assert.IsTrue(document.Diagnostics.All(d => d.Severity != DiagnosticSeverity.Error));
    }

    [TestMethod]
    public async Task DocumentWithNoValidTokensCanBeOpened() {
      var source = "";
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var document = await Documents.GetResolvedDocumentAsync(documentItem.Uri);
      Assert.IsNotNull(document);
      Assert.IsTrue(document.Diagnostics.All(d => d.Severity != DiagnosticSeverity.Error));
    }

    [TestMethod]
    public async Task EmptyDocumentCanBeIncluded() {
      var source = "include \"empty.dfy\"";
      var documentItem = CreateTestDocument(source, Path.Combine(Directory.GetCurrentDirectory(), "Synchronization/TestFiles/test.dfy"));
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var document = await Documents.GetResolvedDocumentAsync(documentItem.Uri);
      Assert.IsNotNull(document);
      Assert.IsTrue(!document.Diagnostics.Any());
    }
  }
}
