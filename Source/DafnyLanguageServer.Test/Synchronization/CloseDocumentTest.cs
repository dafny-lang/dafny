using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using OmniSharp.Extensions.LanguageServer.Protocol.Client;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Threading.Tasks;
using Xunit;
using Xunit.Abstractions;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Synchronization {
  public class CloseDocumentTest : DafnyLanguageServerTestBase, IAsyncLifetime {
    private ILanguageClient client;

    public async Task InitializeAsync() {
      client = await InitializeClient();
    }

    public Task DisposeAsync() {
      return Task.CompletedTask;
    }

    private Task CloseDocumentAndWaitAsync(TextDocumentItem documentItem) {
      client.DidCloseTextDocument(new DidCloseTextDocumentParams {
        TextDocument = documentItem
      });
      return client.WaitForNotificationCompletionAsync(documentItem.Uri, CancellationToken);
    }

    [Fact]
    public async Task DocumentIsUnloadedWhenClosed() {
      var source = @"
function GetConstant(): int {
  1
}".Trim();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await CloseDocumentAndWaitAsync(documentItem);
      Assert.Null(await Documents.GetResolvedDocumentAsync(documentItem.Uri));
    }

    [Fact]
    public async Task DocumentStaysUnloadedWhenClosed() {
      var source = @"
function GetConstant(): int {
  1
}".Trim();
      var documentItem = CreateTestDocument(source);
      await CloseDocumentAndWaitAsync(documentItem);
      Assert.Null(await Documents.GetResolvedDocumentAsync(documentItem.Uri));
    }

    public CloseDocumentTest(ITestOutputHelper output) : base(output) {
    }
  }
}
