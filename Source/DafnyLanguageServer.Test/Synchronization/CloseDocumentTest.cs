using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using OmniSharp.Extensions.LanguageServer.Protocol.Client;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Threading.Tasks;
using Xunit.Abstractions;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Synchronization {
  [TestClass]
  public class CloseDocumentTest : DafnyLanguageServerTestBase {
    private ILanguageClient client;

    [TestInitialize]
    public async Task SetUp() {
      client = await InitializeClient();
    }

    private Task CloseDocumentAndWaitAsync(TextDocumentItem documentItem) {
      client.DidCloseTextDocument(new DidCloseTextDocumentParams {
        TextDocument = documentItem
      });
      return client.WaitForNotificationCompletionAsync(documentItem.Uri, CancellationToken);
    }

    [TestMethod]
    public async Task DocumentIsUnloadedWhenClosed() {
      var source = @"
function GetConstant(): int {
  1
}".Trim();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await CloseDocumentAndWaitAsync(documentItem);
      Assert.IsNull(await Documents.GetResolvedDocumentAsync(documentItem.Uri));
    }

    [TestMethod]
    public async Task DocumentStaysUnloadedWhenClosed() {
      var source = @"
function GetConstant(): int {
  1
}".Trim();
      var documentItem = CreateTestDocument(source);
      await CloseDocumentAndWaitAsync(documentItem);
      Assert.IsNull(await Documents.GetResolvedDocumentAsync(documentItem.Uri));
    }

    public CloseDocumentTest(ITestOutputHelper output) : base(output)
    {
    }
  }
}
