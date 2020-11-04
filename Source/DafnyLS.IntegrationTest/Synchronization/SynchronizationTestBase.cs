using DafnyLS.IntegrationTest.Extensions;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using OmniSharp.Extensions.LanguageServer.Protocol.Client;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Threading.Tasks;

namespace DafnyLS.IntegrationTest.Synchronization {
  public class SynchronizationTestBase : DafnyLanguageServerTestBase {
    protected ILanguageClient Client { get; private set; }

    protected Task ApplyChangeAndWaitCompletionAsync(TextDocumentItem documentItem, Range range, string newText) {
      Client.DidChangeTextDocument(new DidChangeTextDocumentParams {
        TextDocument = new VersionedTextDocumentIdentifier {
          Uri = documentItem.Uri,
          Version = documentItem.Version + 1
        },
        ContentChanges = new[] {
          new TextDocumentContentChangeEvent {
            Text = newText,
            Range = range
          }
        }
      });
      return Client.WaitForNotificationCompletionAsync(documentItem.Uri, CancellationToken);
    }

    [TestInitialize]
    public async Task SetUp() {
      Client = await InitializeClient();
    }
  }
}
