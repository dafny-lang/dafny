using System.Linq;
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
      (client, Server) = await Initialize(_ => { }, _ => { });
    }

    public Task DisposeAsync() {
      return Task.CompletedTask;
    }

    [Fact]
    public async Task DocumentIsUnloadedWhenClosed() {
      var source = @"
function GetConstant(): int {
  1
}".Trim();
      var documentItem = CreateTestDocument(source, "DocumentIsUnloadedWhenClosed.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      client.CloseDocument(documentItem);
      for (int attempt = 0; attempt < 50; attempt++) {
        if (!Projects.Managers.Any()) {
          return;
        }

        await Task.Delay(100);
      }
      Assert.Fail("all attempts failed");
    }

    [Fact]
    public async Task DocumentStaysUnloadedWhenClosed() {
      var source = @"
function GetConstant(): int {
  1
}".Trim();
      var documentItem = CreateTestDocument(source, "DocumentStaysUnloadedWhenClosed.dfy");
      client.CloseDocument(documentItem);
      Assert.Null(await Projects.GetResolvedDocumentAsyncNormalizeUri(documentItem.Uri));
    }

    public CloseDocumentTest(ITestOutputHelper output) : base(output) {
    }
  }
}
