using System;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Various;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Extensions.DependencyInjection;
using Microsoft.Extensions.Logging;
using Microsoft.Extensions.Options;
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
    client = await InitializeClient(options => {
      options.OnPublishDiagnostics(diagnosticReceiver.NotificationReceived);
    }, serverOptions => {
      serverOptions.Services.AddSingleton<IProgramVerifier>(serviceProvider => new SlowVerifier(
        serviceProvider.GetRequiredService<ILogger<DafnyProgramVerifier>>(),
        serviceProvider.GetRequiredService<IOptions<VerifierOptions>>()
      ));
    });
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

  public async Task AssertNoDiagnosticsAreComing() {
    foreach (var entry in Documents.Documents.Values) {
      try {
        await entry.VerifiedDocument;
      } catch (TaskCanceledException) {

      }
    }
    var verificationDocumentItem = CreateTestDocument("class X {does not parse", $"verification{fileIndex++}.dfy");
    await client.OpenDocumentAndWaitAsync(verificationDocumentItem, CancellationToken.None);
    var resolutionReport = await diagnosticReceiver.AwaitNextNotificationAsync(CancellationToken.None);
    Assert.AreEqual(verificationDocumentItem.Uri, resolutionReport.Uri);
    client.DidCloseTextDocument(new DidCloseTextDocumentParams {
      TextDocument = verificationDocumentItem
    });
    var hideReport = await diagnosticReceiver.AwaitNextNotificationAsync(CancellationToken.None);
    Assert.AreEqual(verificationDocumentItem.Uri, hideReport.Uri);
  }
}