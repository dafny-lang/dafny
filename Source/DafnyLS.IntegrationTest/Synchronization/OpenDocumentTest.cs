using DafnyLS.IntegrationTest.Extensions;
using Microsoft.Dafny;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using OmniSharp.Extensions.LanguageServer.Protocol.Client;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Threading.Tasks;

namespace DafnyLS.IntegrationTest {
  [TestClass]
  public class OpenDocumentTest : DafnyLanguageServerTestBase {
    private ILanguageClient _client;

    private Task OpenDocumentAsync(TextDocumentItem documentItem) {
      // The underlying implementation of OpenDocument is non-blocking (DidOpenTextDocument).
      // Since we query the document database directly, we use a placeholder request to ensure
      // that the DidOpenTextDocument has been fully processed.
      _client.OpenDocument(documentItem);
      return _client.RequestHover(new HoverParams { Position = (0, 0), TextDocument = documentItem.Uri }, CancellationToken);
    }

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
      await OpenDocumentAsync(documentItem);
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
      await OpenDocumentAsync(documentItem);
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
      await OpenDocumentAsync(documentItem);
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
      await OpenDocumentAsync(documentItem);
      Assert.IsTrue(Documents.TryGetDocument(documentItem.Uri, out var document));
      Assert.AreEqual(1, document.Errors.AllMessages[ErrorLevel.Error].Count);
      var message = document.Errors.AllMessages[ErrorLevel.Error][0];
      Assert.AreEqual(MessageSource.Other, message.source);
    }
  }
}
