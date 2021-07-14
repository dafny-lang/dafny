using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using OmniSharp.Extensions.LanguageServer.Protocol.Client;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Threading.Tasks;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Synchronization {
  [TestClass]
  public class CloseDocumentTest : DafnyLanguageServerTestBase {
    private ILanguageClient _client;

    [TestInitialize]
    public async Task SetUp() {
      _client = await InitializeClient();
    }

    private Task CloseDocumentAndWaitAsync(TextDocumentItem documentItem) {
      _client.DidCloseTextDocument(new DidCloseTextDocumentParams {
        TextDocument = documentItem
      });
      return _client.WaitForNotificationCompletionAsync(documentItem.Uri, CancellationToken);
    }

    [TestMethod]
    public async Task DocumentIsUnloadedWhenClosed() {
      var source = @"
function GetConstant(): int {
  1
}".Trim();
      var documentItem = CreateTestDocument(source);
      await _client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await CloseDocumentAndWaitAsync(documentItem);
      Assert.IsFalse(Documents.TryGetDocument(documentItem.Uri, out var _));
    }

    [TestMethod]
    public async Task DocumentStaysUnloadedWhenClosed() {
      var source = @"
function GetConstant(): int {
  1
}".Trim();
      var documentItem = CreateTestDocument(source);
      await CloseDocumentAndWaitAsync(documentItem);
      Assert.IsFalse(Documents.TryGetDocument(documentItem.Uri, out var _));
    }
  }
}
