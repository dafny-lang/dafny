using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using System.Reactive.Threading.Tasks;
using System.Text.RegularExpressions;
using System.Threading;
using System.Threading.Tasks;
using JetBrains.Annotations;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using OmniSharp.Extensions.JsonRpc;
using OmniSharp.Extensions.LanguageServer.Client;
using OmniSharp.Extensions.LanguageServer.Protocol.Client;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Xunit.Abstractions;
using Xunit;
using XunitAssertMessages;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Util;

public class ClientBasedLanguageServerTest : DafnyLanguageServerTestBase, IAsyncLifetime {

  protected ILanguageClient client;
  protected TestNotificationReceiver<FileVerificationStatus> verificationStatusReceiver;
  protected TestNotificationReceiver<CompilationStatusParams> compilationStatusReceiver;
  protected DiagnosticsReceiver diagnosticsReceiver;
  protected TestNotificationReceiver<GhostDiagnosticsParams> ghostnessReceiver;

  private const int MaxRequestExecutionTimeMs = 180_000;

  // We do not use the LanguageServerTestBase.cancellationToken here because it has a timeout.
  // Since these tests are slow, we do not use the timeout here.
  private CancellationTokenSource cancellationSource;

  protected CancellationToken CancellationTokenWithHighTimeout => cancellationSource.Token;

  private static Regex errorTests = new Regex(@"\*\*Error:\*\*|\*\*Success:\*\*");


  protected async Task<TextDocumentItem> CreateAndOpenTestDocument(string source, string filePath = null,
    int version = 1) {
    var document = CreateTestDocument(source, filePath, version);
    await client.OpenDocumentAndWaitAsync(document, CancellationToken);
    return document;
  }

  protected async Task AssertHoverMatches(TextDocumentItem documentItem, Position hoverPosition, [CanBeNull] string expected) {
    if (expected != null && errorTests.Matches(expected).Count >= 2) {
      Assert.Fail("Found multiple hover messages in one test; the order is currently not stable, so please test one at a time.");
    }
    var hover = await RequestHover(documentItem, hoverPosition);
    if (expected == null) {
      Assert.True(hover == null || hover.Contents.MarkupContent is null or { Value: "" });
      return;
    }
    AssertM.NotNull(hover, $"No hover message found at {hoverPosition}");
    var markup = hover.Contents.MarkupContent;
    Assert.NotNull(markup);
    Assert.Equal(MarkupKind.Markdown, markup.Kind);
    AssertMatchRegex(expected.ReplaceLineEndings("\n"), markup.Value);
  }

  private Task<Hover> RequestHover(TextDocumentItem documentItem, Position position) {
    return client.RequestHover(
      new HoverParams {
        TextDocument = documentItem.Uri,
        Position = position
      },
      CancellationToken
    );
  }

  private void AssertMatchRegex(string expected, string value) {
    var regexExpected = Regex.Escape(expected).Replace(@"\?\?\?", "[\\s\\S]*");
    var matched = new Regex(regexExpected).Match(value).Success;
    if (!matched) {
      // A simple helper to determine what portion of the regex did not match
      var helper = "";
      foreach (var chunk in expected.Split("???")) {
        if (!value.Contains(chunk)) {
          helper += $"\nThe result string did not contain '{chunk}'";
        }
      }
      Assert.Fail($"{value} did not match {regexExpected}." + helper);
    }
  }

  public async Task<NamedVerifiableStatus> WaitForStatus(Range nameRange, PublishedVerificationStatus statusToFind,
    CancellationToken cancellationToken, [CanBeNull] TextDocumentIdentifier documentIdentifier = null) {
    while (true) {
      try {
        var foundStatus = await verificationStatusReceiver.AwaitNextNotificationAsync(cancellationToken);
        var namedVerifiableStatus = foundStatus.NamedVerifiables.FirstOrDefault(n => n.NameRange == nameRange);
        if (namedVerifiableStatus?.Status == statusToFind) {
          if (documentIdentifier != null) {
            Assert.Equal(documentIdentifier.Uri, foundStatus.Uri);
          }

          return namedVerifiableStatus;
        }
      } catch (OperationCanceledException) {
        await output.WriteLineAsync($"\nOld to new history was: {verificationStatusReceiver.History.Stringify()}");
      }
    }
  }

  public async Task<IList<FileVerificationStatus>> WaitUntilCompletedForUris(int uriCount, CancellationToken cancellationToken) {
    var result = new List<FileVerificationStatus>();
    var donePerUri = new Dictionary<Uri, bool>();
    while (true) {

      if (donePerUri.Count == uriCount && donePerUri.Values.All(x => x)) {
        break;
      }

      try {
        var foundStatus = await verificationStatusReceiver.AwaitNextNotificationAsync(cancellationToken);
        donePerUri[foundStatus.Uri.ToUri()] =
          foundStatus.NamedVerifiables.All(n => n.Status >= PublishedVerificationStatus.Error);
        result.Add(foundStatus);
      } catch (OperationCanceledException) {
        await output.WriteLineAsync($"\nOld to new history was: {verificationStatusReceiver.History.Stringify()}");
        throw;
      }
    }

    return result;
  }

  public async Task<IEnumerable<DocumentSymbol>> RequestDocumentSymbol(TextDocumentItem documentItem) {
    var things = await client.RequestDocumentSymbol(
      new DocumentSymbolParams {
        TextDocument = documentItem.Uri,
      },
      CancellationToken
    ).ToTask();

    return things.Select(t => t.DocumentSymbol!);
  }

  public async Task<PublishDiagnosticsParams> GetLastDiagnosticsParams(TextDocumentItem documentItem, CancellationToken cancellationToken) {
    await client.WaitForNotificationCompletionAsync(documentItem.Uri, cancellationToken);
    var compilation = (await Projects.GetLastDocumentAsync(documentItem))!;
    Assert.NotNull(compilation);
    var expectedDiagnostics = compilation.GetDiagnostics(documentItem.Uri.ToUri()).Select(d => d.ToLspDiagnostic()).ToList();
    PublishDiagnosticsParams result;
    while (true) {
      result = await diagnosticsReceiver.AwaitNextNotificationAsync(cancellationToken);
      if (result.Uri == documentItem.Uri && result.Diagnostics.SequenceEqual(expectedDiagnostics)) {
        break;
      }
    }

    return result;
  }

  public async Task<Diagnostic[]> GetLastDiagnostics(TextDocumentItem documentItem, CancellationToken cancellationToken) {
    var paramsResult = await GetLastDiagnosticsParams(documentItem, CancellationToken);
    return paramsResult.Diagnostics.ToArray();
  }

  public virtual Task InitializeAsync() {
    return SetUp(null);
  }

  public Task DisposeAsync() {
    return Task.CompletedTask;
  }

  protected virtual async Task SetUp(Action<DafnyOptions> modifyOptions) {

    // We use a custom cancellation token with a higher timeout to clearly identify where the request got stuck.
    cancellationSource = new();
    cancellationSource.CancelAfter(MaxRequestExecutionTimeMs);

    diagnosticsReceiver = new();
    compilationStatusReceiver = new();
    verificationStatusReceiver = new();
    ghostnessReceiver = new();
    (client, Server) = await Initialize(InitialiseClientHandler, modifyOptions);
  }

  protected virtual void InitialiseClientHandler(LanguageClientOptions options) {
    options.OnPublishDiagnostics(diagnosticsReceiver.NotificationReceived);
    options.AddHandler(DafnyRequestNames.CompilationStatus,
      NotificationHandler.For<CompilationStatusParams>(compilationStatusReceiver.NotificationReceived));
    options.AddHandler(DafnyRequestNames.GhostDiagnostics,
      NotificationHandler.For<GhostDiagnosticsParams>(ghostnessReceiver.NotificationReceived));
    options.AddHandler(DafnyRequestNames.VerificationSymbolStatus,
      NotificationHandler.For<FileVerificationStatus>(verificationStatusReceiver.NotificationReceived));
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
    foreach (var entry in Projects.Managers) {
      try {
        await entry.GetLastDocumentAsync();
      } catch (TaskCanceledException) {

      }
    }
    var verificationDocumentItem = CreateTestDocument("method Foo() { assert false; }", $"verification{fileIndex++}.dfy");
    await client.OpenDocumentAndWaitAsync(verificationDocumentItem, CancellationToken);
    var statusReport = await verificationStatusReceiver.AwaitNextNotificationAsync(cancellationToken);
    Assert.Equal(verificationDocumentItem.Uri, statusReport.Uri);
    client.DidCloseTextDocument(new DidCloseTextDocumentParams {
      TextDocument = verificationDocumentItem
    });
  }

  public async Task AssertNoGhostnessIsComing(CancellationToken cancellationToken) {
    foreach (var entry in Projects.Managers) {
      try {
        await entry.GetLastDocumentAsync();
      } catch (TaskCanceledException) {

      }
    }
    var verificationDocumentItem = CreateTestDocument(@"class X {does not parse", $"verification{fileIndex++}.dfy");
    await client.OpenDocumentAndWaitAsync(verificationDocumentItem, CancellationToken);
    var resolutionReport = await diagnosticsReceiver.AwaitNextNotificationAsync(cancellationToken);
    AssertM.Equal(verificationDocumentItem.Uri, resolutionReport.Uri,
      "Unexpected diagnostics were received whereas none were expected:\n" +
      string.Join(",", resolutionReport.Diagnostics.Select(diagnostic =>
        diagnostic.ToString())));
    client.DidCloseTextDocument(new DidCloseTextDocumentParams {
      TextDocument = verificationDocumentItem
    });
    var hideReport = await diagnosticsReceiver.AwaitNextNotificationAsync(cancellationToken);
    Assert.Equal(verificationDocumentItem.Uri, hideReport.Uri);
  }

  public async Task AssertNoDiagnosticsAreComing(CancellationToken cancellationToken, bool waitFirst = true) {
    if (waitFirst) {
      foreach (var entry in Projects.Managers) {
        try {
          await entry.GetLastDocumentAsync();
        } catch (TaskCanceledException) {

        }
      }
    }
    var verificationDocumentItem = CreateTestDocument("class X {does not parse", $"AssertNoDiagnosticsAreComing{fileIndex++}.dfy");
    await client.OpenDocumentAndWaitAsync(verificationDocumentItem, CancellationToken);
    var resolutionReport = await diagnosticsReceiver.AwaitNextNotificationAsync(cancellationToken);
    AssertM.Equal(verificationDocumentItem.Uri, resolutionReport.Uri,
      "1) Unexpected diagnostics were received whereas none were expected:\n" +
      string.Join(",", resolutionReport.Diagnostics.Select(diagnostic => diagnostic.ToString())));
    client.DidCloseTextDocument(new DidCloseTextDocumentParams {
      TextDocument = verificationDocumentItem
    });
    var hideReport = await diagnosticsReceiver.AwaitNextNotificationAsync(cancellationToken);
    AssertM.Equal(verificationDocumentItem.Uri, hideReport.Uri,
      "2) Unexpected diagnostics were received whereas none were expected:\n" +
      string.Join(",", hideReport.Diagnostics.Select(diagnostic => diagnostic.ToString())));
  }

  protected async Task AssertNoResolutionErrors(TextDocumentItem documentItem) {
    var fullDiagnostics = (await Projects.GetResolvedDocumentAsyncNormalizeUri(documentItem))!.GetDiagnostics();
    // A document without diagnostics may be absent, even if resolved successfully
    var resolutionDiagnostics = fullDiagnostics.GetValueOrDefault(documentItem.Uri.ToUri(), ImmutableList<Diagnostic>.Empty);
    var resolutionErrors = resolutionDiagnostics.Count(d => d.Severity == DiagnosticSeverity.Error);
    if (0 != resolutionErrors) {
      await Console.Out.WriteAsync(string.Join("\n", resolutionDiagnostics.Where(d => d.Severity == DiagnosticSeverity.Error).Select(d => d.ToString())));
      Assert.Equal(0, resolutionErrors);
    }
  }

  public async Task<PublishedVerificationStatus> PopNextStatus() {
    var nextNotification = await verificationStatusReceiver.AwaitNextNotificationAsync(CancellationToken);
    Assert.NotNull(nextNotification);
    Assert.Equal(1, nextNotification.NamedVerifiables.Count);
    return nextNotification.NamedVerifiables.Single().Status;
  }

  protected Task<LocationOrLocationLinks> RequestDefinition(TextDocumentItem documentItem, Position position) {
    return client.RequestDefinition(
      new DefinitionParams {
        TextDocument = documentItem.Uri,
        Position = position
      },
      CancellationToken
    ).AsTask();
  }

  protected Task ApplyChangesAndWaitCompletionAsync(TextDocumentItem documentItem,
    params TextDocumentContentChangeEvent[] changes) {
    return ApplyChangesAndWaitCompletionAsync(new VersionedTextDocumentIdentifier() {
      Version = documentItem.Version!.Value,
      Uri = documentItem.Uri
    }, changes);
  }

  protected Task ApplyChangesAndWaitCompletionAsync(VersionedTextDocumentIdentifier documentItem, params TextDocumentContentChangeEvent[] changes) {
    client.DidChangeTextDocument(new DidChangeTextDocumentParams {
      TextDocument = new OptionalVersionedTextDocumentIdentifier {
        Uri = documentItem.Uri,
        Version = documentItem.Version + 1
      },
      ContentChanges = changes
    });
    return client.WaitForNotificationCompletionAsync(documentItem.Uri, CancellationToken);
  }

  public ClientBasedLanguageServerTest(ITestOutputHelper output) : base(output) {
  }
}
