using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using OmniSharp.Extensions.LanguageServer.Protocol.Client;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Threading.Tasks;
using Xunit;
using Xunit.Abstractions;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Synchronization {
  public class SynchronizationTestBase : DafnyLanguageServerTestBase, IAsyncLifetime {
    protected ILanguageClient Client { get; set; }

    public virtual async Task InitializeAsync() {
      Client = await InitializeClient();
    }

    public Task DisposeAsync() {
      return Task.CompletedTask;
    }

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

    public SynchronizationTestBase(ITestOutputHelper output) : base(output)
    {
    }
  }
}
