using System;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using OmniSharp.Extensions.LanguageServer.Protocol.Client;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Util; 

public class ClientBasedLanguageServerTest : DafnyLanguageServerTestBase {
  protected ILanguageClient client;
  protected DiagnosticsReceiver diagnosticReceiver;

  [TestInitialize]
  public virtual async Task SetUp() {
    diagnosticReceiver = new();
    client = await InitializeClient(options => options.OnPublishDiagnostics(diagnosticReceiver.NotificationReceived));
  }

  protected void ApplyChange(ref TextDocumentItem documentItem, Range range, string text) {
    documentItem = documentItem with { Version = documentItem.Version + 1 };
    client.DidChangeTextDocument(new DidChangeTextDocumentParams {
      TextDocument = new OptionalVersionedTextDocumentIdentifier {
        Uri = documentItem.Uri,
        Version = documentItem.Version
      },
      ContentChanges = new[] {
        new TextDocumentContentChangeEvent {
          Range = range,
          Text = text
        }
      }
    });
  }

  public async Task<bool> DidMoreDiagnosticsCome() {
    var verificationDocumentItem = CreateTestDocument("class X {}", $"verification{new Random().Next()}.dfy");
    await client.OpenDocumentAndWaitAsync(verificationDocumentItem, CancellationToken.None);
    await diagnosticReceiver.AwaitNextNotificationAsync(CancellationToken.None);
    var verificationReport = await diagnosticReceiver.AwaitNextNotificationAsync(CancellationToken.None);
    client.DidCloseTextDocument(new DidCloseTextDocumentParams {
      TextDocument = verificationDocumentItem
    });
    return verificationDocumentItem.Uri != verificationReport.Uri;
  }
}