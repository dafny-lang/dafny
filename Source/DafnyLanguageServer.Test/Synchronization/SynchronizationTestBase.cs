﻿using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using OmniSharp.Extensions.LanguageServer.Protocol.Client;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Threading.Tasks;
using Microsoft.Extensions.Logging;
using Xunit;
using Xunit.Abstractions;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Synchronization {
  public class SynchronizationTestBase : DafnyLanguageServerTestBase, IAsyncLifetime {
    protected ILanguageClient Client { get; set; }

    public virtual async Task InitializeAsync() {
      (Client, Server) = await Initialize(_ => { }, _ => { });
    }

    public Task DisposeAsync() {
      return Task.CompletedTask;
    }

    protected Task ApplyChangeAndWaitCompletionAsync(ref TextDocumentItem documentItem, Range range,
      string newText) {
      var versionedTextDocumentIdentifier = new VersionedTextDocumentIdentifier() {
        Version = documentItem.Version!.Value,
        Uri = documentItem.Uri
      };
      documentItem = documentItem with { Version = documentItem.Version + 1 };
      return ApplyChangeAndWaitCompletionAsync(versionedTextDocumentIdentifier, range, newText);
    }

    protected Task ApplyChangeAndWaitCompletionAsync(VersionedTextDocumentIdentifier documentItem, Range range, string newText) {
      return ApplyChangesAndWaitCompletionAsync(
        documentItem,
        new TextDocumentContentChangeEvent {
          Text = newText,
          Range = range
        }
      );
    }

    protected Task ApplyChangesAndWaitCompletionAsync(TextDocumentItem documentItem,
      params TextDocumentContentChangeEvent[] changes) {
      return ApplyChangesAndWaitCompletionAsync(new VersionedTextDocumentIdentifier() {
        Version = documentItem.Version!.Value,
        Uri = documentItem.Uri
      }, changes);
    }

    protected Task ApplyChangesAndWaitCompletionAsync(VersionedTextDocumentIdentifier documentItem, params TextDocumentContentChangeEvent[] changes) {
      Client.DidChangeTextDocument(new DidChangeTextDocumentParams {
        TextDocument = new OptionalVersionedTextDocumentIdentifier {
          Uri = documentItem.Uri,
          Version = documentItem.Version + 1
        },
        ContentChanges = changes
      });
      return Client.WaitForNotificationCompletionAsync(documentItem.Uri, CancellationToken);
    }

    public SynchronizationTestBase(ITestOutputHelper output, LogLevel logLevel = LogLevel.Information) : base(output, logLevel) {
    }
  }
}
