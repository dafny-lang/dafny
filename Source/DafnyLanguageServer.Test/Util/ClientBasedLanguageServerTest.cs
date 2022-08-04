using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Linq;
using System.Runtime.CompilerServices;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Various;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using Microsoft.Extensions.Configuration;
using Microsoft.Extensions.DependencyInjection;
using Microsoft.Extensions.Logging;
using Microsoft.Extensions.Options;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using OmniSharp.Extensions.JsonRpc;
using OmniSharp.Extensions.LanguageServer.Client;
using OmniSharp.Extensions.LanguageServer.Protocol.Client;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using OmniSharp.Extensions.LanguageServer.Server;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Util; 

public class ClientBasedLanguageServerTest : DafnyLanguageServerTestBase {
  protected ILanguageClient client;
  protected TestNotificationReceiver<FileVerificationStatus> verificationStatusReceiver;
  private IDictionary<string, string> configuration;
  protected DiagnosticsReceiver diagnosticsReceiver;
  protected TestNotificationReceiver<GhostDiagnosticsParams> ghostnessReceiver;

  public async Task<NamedVerifiableStatus> WaitForStatus(Range nameRange, PublishedVerificationStatus statusToFind,
    CancellationToken cancellationToken) {
    while (true) {
      var foundStatus = await verificationStatusReceiver.AwaitNextNotificationAsync(cancellationToken);
      var namedVerifiableStatus = foundStatus.NamedVerifiables.FirstOrDefault(n => n.NameRange == nameRange);
      if (namedVerifiableStatus?.Status == statusToFind) {
        return namedVerifiableStatus;
      }
    }
  }

  public async Task<Diagnostic[]> GetLastDiagnostics(TextDocumentItem documentItem, CancellationToken cancellationToken) {
    await client.WaitForNotificationCompletionAsync(documentItem.Uri, cancellationToken);
    var document = await Documents.GetLastDocumentAsync(documentItem);
    Diagnostic[] result;
    do {
      result = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(cancellationToken);
    } while (!document!.Diagnostics.SequenceEqual(result));

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
    diagnosticsReceiver = new();
    verificationStatusReceiver = new();
    ghostnessReceiver = new();
    client = await InitializeClient(InitialiseClientHandler, serverOptions => {
      ServerOptionsAction(serverOptions);
    });
  }

  protected virtual void InitialiseClientHandler(LanguageClientOptions options) {
    options.OnPublishDiagnostics(diagnosticsReceiver.NotificationReceived);
    options.AddHandler(DafnyRequestNames.GhostDiagnostics,
      NotificationHandler.For<GhostDiagnosticsParams>(ghostnessReceiver.NotificationReceived));
    options.AddHandler(DafnyRequestNames.VerificationSymbolStatus,
      NotificationHandler.For<FileVerificationStatus>(verificationStatusReceiver.NotificationReceived));
  }

  protected virtual IServiceCollection ServerOptionsAction(LanguageServerOptions serverOptions) {
    return serverOptions.Services.AddSingleton<IProgramVerifier>(serviceProvider => new SlowVerifier(
      serviceProvider.GetRequiredService<ILogger<DafnyProgramVerifier>>(),
      serviceProvider.GetRequiredService<IOptions<VerifierOptions>>()
    ));
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

  public async Task AssertNoVerificationStatusIsComing(TextDocumentItem documentItem, CancellationToken cancellationToken) {
    foreach (var entry in Documents.Documents) {
      try {
        await entry.LastDocument;
      } catch (TaskCanceledException) {

      }
    }
    var verificationDocumentItem = CreateTestDocument("method Foo() { assert false; }", $"verification{fileIndex++}.dfy");
    await client.OpenDocumentAndWaitAsync(verificationDocumentItem, CancellationToken.None);
    var statusReport = await verificationStatusReceiver.AwaitNextNotificationAsync(cancellationToken);
    Assert.AreEqual(verificationDocumentItem.Uri, statusReport.Uri);
    client.DidCloseTextDocument(new DidCloseTextDocumentParams {
      TextDocument = verificationDocumentItem
    });
  }

  public async Task AssertNoGhostnessIsComing(CancellationToken cancellationToken) {
    foreach (var entry in Documents.Documents) {
      try {
        await entry.LastDocument;
      } catch (TaskCanceledException) {

      }
    }
    var verificationDocumentItem = CreateTestDocument(@"class X {does not parse", $"verification{fileIndex++}.dfy");
    await client.OpenDocumentAndWaitAsync(verificationDocumentItem, CancellationToken.None);
    var resolutionReport = await diagnosticsReceiver.AwaitNextNotificationAsync(cancellationToken);
    Assert.AreEqual(verificationDocumentItem.Uri, resolutionReport.Uri,
      "Unexpected diagnostics were received whereas none were expected:\n" +
      string.Join(",", resolutionReport.Diagnostics.Select(diagnostic =>
        diagnostic.ToString())));
    client.DidCloseTextDocument(new DidCloseTextDocumentParams {
      TextDocument = verificationDocumentItem
    });
    var hideReport = await diagnosticsReceiver.AwaitNextNotificationAsync(cancellationToken);
    Assert.AreEqual(verificationDocumentItem.Uri, hideReport.Uri);
  }

  public async Task AssertNoDiagnosticsAreComing(CancellationToken cancellationToken) {
    foreach (var entry in Documents.Documents) {
      try {
        await entry.LastDocument;
      } catch (TaskCanceledException) {

      }
    }
    var verificationDocumentItem = CreateTestDocument("class X {does not parse", $"verification{fileIndex++}.dfy");
    await client.OpenDocumentAndWaitAsync(verificationDocumentItem, CancellationToken.None);
    var resolutionReport = await diagnosticsReceiver.AwaitNextNotificationAsync(cancellationToken);
    Assert.AreEqual(verificationDocumentItem.Uri, resolutionReport.Uri,
      "1) Unexpected diagnostics were received whereas none were expected:\n" +
      string.Join(",", resolutionReport.Diagnostics.Select(diagnostic => diagnostic.ToString())));
    client.DidCloseTextDocument(new DidCloseTextDocumentParams {
      TextDocument = verificationDocumentItem
    });
    var hideReport = await diagnosticsReceiver.AwaitNextNotificationAsync(cancellationToken);
    Assert.AreEqual(verificationDocumentItem.Uri, hideReport.Uri,
      "2) Unexpected diagnostics were received whereas none were expected:\n" +
      string.Join(",", hideReport.Diagnostics.Select(diagnostic => diagnostic.ToString())));
  }

  protected async Task AssertNoResolutionErrors(TextDocumentItem documentItem) {
    var resolutionDiagnostics = (await Documents.GetResolvedDocumentAsync(documentItem))!.Diagnostics;
    Assert.AreEqual(0, resolutionDiagnostics.Count(d => d.Severity == DiagnosticSeverity.Error));
  }
}