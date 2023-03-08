using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using OmniSharp.Extensions.LanguageServer.Protocol.Client;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Threading.Tasks;
using Xunit.Abstractions;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Synchronization {
  public class SynchronizationTestBase : DafnyLanguageServerTestBase {
    protected ILanguageClient Client { get; set; }

    protected Task ApplyChangeAndWaitCompletionAsync(TextDocumentItem documentItem, Range range, string newText) {
      return ApplyChangesAndWaitCompletionAsync(
        documentItem,
        new TextDocumentContentChangeEvent {
          Text = newText,
          Range = range
        }
      );
    }

    protected Task ApplyChangesAndWaitCompletionAsync(TextDocumentItem documentItem, params TextDocumentContentChangeEvent[] changes) {
      Client.DidChangeTextDocument(new DidChangeTextDocumentParams {
        TextDocument = new OptionalVersionedTextDocumentIdentifier {
          Uri = documentItem.Uri,
          Version = documentItem.Version + 1
        },
        ContentChanges = changes
      });
      return Client.WaitForNotificationCompletionAsync(documentItem.Uri, CancellationToken);
    }

    [TestInitialize]
    public async Task SetUp() {
      Client = await InitializeClient();
    }

    public SynchronizationTestBase(ITestOutputHelper output) : base(output)
    {
    }
  }
}
