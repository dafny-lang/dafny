using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Various;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Extensions.Configuration;
using Microsoft.Extensions.DependencyInjection;
using Microsoft.Extensions.Logging;
using Microsoft.Extensions.Options;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using OmniSharp.Extensions.JsonRpc;
using OmniSharp.Extensions.LanguageServer.Protocol.Client;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Util; 

public class ClientBasedLanguageServerTest : DafnyLanguageServerTestBase {
  protected ILanguageClient client;
  protected DiagnosticsReceiver diagnosticReceiver;
  protected TestNotificationReceiver<FileVerificationStatus> verificationStatusReceiver;
  private IDictionary<string, string> configuration;

  public async Task<Diagnostic[]> GetLastVerificationDiagnostics(TextDocumentItem documentItem, CancellationToken cancellationToken = default, int? expectedNumber = null) {
    await client.WaitForNotificationCompletionAsync(documentItem.Uri, cancellationToken);
    var document = await Documents.GetVerifiedDocumentAsync(documentItem);
    var remainingDiagnostics = expectedNumber ?? Int32.MaxValue;
    Diagnostic[] result = null;
    do {
      var newDiagnostics = await diagnosticReceiver.AwaitNextDiagnosticsAsync(cancellationToken);
      if (result != null) {
        Assert.AreNotEqual(result, newDiagnostics);
      }
      result = newDiagnostics;
      remainingDiagnostics--;
    } while (!document!.Diagnostics.SequenceEqual(result) && remainingDiagnostics > 0);
    return result;
  }

  public async Task SetUp(IDictionary<string, string> configuration) {
    this.configuration = configuration;
    await SetUp();
  }

  protected override IConfiguration CreateConfiguration() {
    return configuration == null
      ? base.CreateConfiguration()
      : new ConfigurationBuilder().AddInMemoryCollection(configuration).Build();
  }

  [TestInitialize]
  public virtual async Task SetUp() {

    diagnosticReceiver = new();
    verificationStatusReceiver = new();
    client = await InitializeClient(options => {
      options.OnPublishDiagnostics(diagnosticReceiver.NotificationReceived);
      options.AddHandler(DiagnosticPublisher.VerificationStatusNotification, NotificationHandler.For<FileVerificationStatus>(verificationStatusReceiver.NotificationReceived));
    }, serverOptions => {
      serverOptions.Services.AddSingleton<IProgramVerifier>(serviceProvider => new SlowVerifier(
        serviceProvider.GetRequiredService<ILogger<SlowVerifier>>(),
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

  public async Task AssertNoDiagnosticsAreComing(CancellationToken cancellationToken) {
    foreach (var entry in Documents.Documents.Values) {
      try {
        await entry.FullyVerifiedDocument;
      } catch (TaskCanceledException) {

      }
    }
    var verificationDocumentItem = CreateTestDocument("class X {does not parse", $"verification{fileIndex++}.dfy");
    await client.OpenDocumentAndWaitAsync(verificationDocumentItem, CancellationToken.None);
    var resolutionReport = await diagnosticReceiver.AwaitNextNotificationAsync(cancellationToken);
    Assert.AreEqual(verificationDocumentItem.Uri, resolutionReport.Uri);
    client.DidCloseTextDocument(new DidCloseTextDocumentParams {
      TextDocument = verificationDocumentItem
    });
    var hideReport = await diagnosticReceiver.AwaitNextNotificationAsync(cancellationToken);
    Assert.AreEqual(verificationDocumentItem.Uri, hideReport.Uri);
  }

  protected async Task AssertNoResolutionErrors(TextDocumentItem documentItem)
  {
    var resolutionDiagnostics = (await Documents.GetDocumentAsync(documentItem))!.Diagnostics;
    Assert.AreEqual(0, resolutionDiagnostics.Count());
  }
}