using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using OmniSharp.Extensions.LanguageServer.Protocol.Client;
using System.Threading.Tasks;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Synchronization {
  [TestClass]
  public class OpenDocumentTest : DafnyLanguageServerTestBase {
    private ILanguageClient _client;

    [TestInitialize]
    public async Task SetUp() {
      _client = await InitializeClient();
    }

    [TestMethod]
    public async Task CorrectDocumentCanBeParsedResolvedAndVerifiedWithoutErrors() {
      var source = @"
function GetConstant(): int {
  1
}".Trim();
      var documentItem = CreateTestDocument(source);
      await _client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      Assert.IsTrue(Documents.TryGetDocument(documentItem.Uri, out var document));
      Assert.AreEqual(0, document.Errors.AllMessages[ErrorLevel.Error].Count);
    }

    [TestMethod]
    public async Task ParseErrorsOfDocumentAreCaptured() {
      var source = @"
function GetConstant() int {
  1
}".Trim();
      var documentItem = CreateTestDocument(source);
      await _client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      Assert.IsTrue(Documents.TryGetDocument(documentItem.Uri, out var document));
      Assert.AreEqual(1, document.Errors.AllMessages[ErrorLevel.Error].Count);
      var message = document.Errors.AllMessages[ErrorLevel.Error][0];
      Assert.AreEqual(MessageSource.Parser, message.source);
    }

    [TestMethod]
    public async Task SemanticErrorsOfDocumentAreCaptured() {
      var source = @"
function GetConstant(): int {
  ""1""
}".Trim();
      var documentItem = CreateTestDocument(source);
      await _client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      Assert.IsTrue(Documents.TryGetDocument(documentItem.Uri, out var document));
      Assert.AreEqual(1, document.Errors.AllMessages[ErrorLevel.Error].Count);
      var message = document.Errors.AllMessages[ErrorLevel.Error][0];
      Assert.AreEqual(MessageSource.Resolver, message.source);
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
      await _client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      Assert.IsTrue(Documents.TryGetDocument(documentItem.Uri, out var document));
      Assert.AreEqual(1, document.Errors.AllMessages[ErrorLevel.Error].Count);
      var message = document.Errors.AllMessages[ErrorLevel.Error][0];
      Assert.AreEqual(MessageSource.Other, message.source);
    }
  }
}
