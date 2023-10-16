using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.IO;
using System.Linq;
using System.Reactive.Threading.Tasks;
using System.Text.RegularExpressions;
using System.Threading;
using System.Threading.Tasks;
using JetBrains.Annotations;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Dafny.LanguageServer.Workspace.Notifications;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.JsonRpc;
using OmniSharp.Extensions.LanguageServer.Client;
using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Client;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Xunit.Abstractions;
using Xunit;
using Xunit.Sdk;
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

  protected ClientBasedLanguageServerTest(ITestOutputHelper output, LogLevel dafnyLogLevel = LogLevel.Information)
    : base(output, dafnyLogLevel) {
  }

  protected TextDocumentItem CreateAndOpenTestDocument(string source, string filePath = null,
    int version = 1) {
    var document = CreateTestDocument(source, filePath, version);
    client.OpenDocument(document);
    return document;
  }

  protected async Task<TextDocumentItem> CreateOpenAndWaitForResolve(string source, string filePath = null,
    int version = 1, CancellationToken? cancellationToken = null) {
    var document = CreateTestDocument(source, filePath, version);
    await client.OpenDocumentAndWaitAsync(document, cancellationToken ?? CancellationToken);
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

  public async Task<NamedVerifiableStatus> WaitForStatus([CanBeNull] Range nameRange, PublishedVerificationStatus statusToFind,
    CancellationToken cancellationToken, [CanBeNull] TextDocumentIdentifier documentIdentifier = null) {
    while (true) {
      try {
        var foundStatus = await verificationStatusReceiver.AwaitNextNotificationAsync(cancellationToken);
        var namedVerifiableStatus = foundStatus.NamedVerifiables.FirstOrDefault(n => nameRange == null || n.NameRange == nameRange);
        if (namedVerifiableStatus?.Status == statusToFind) {
          if (documentIdentifier != null) {
            Assert.Equal(documentIdentifier.Uri, foundStatus.Uri);
          }

          return namedVerifiableStatus;
        }
      } catch (OperationCanceledException) {
        WriteVerificationHistory();
        throw;
      }
    }
  }

  protected void WriteVerificationHistory() {
    output.WriteLine($"\nOld to new history was:");
    verificationStatusReceiver.History.Stringify(output,
      overrides: StringifyUtil.EmptyOverrides().
        UseToString(typeof(Range)).
        UseToString(typeof(DocumentUri)));
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
        WriteVerificationHistory();
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

  protected async Task<ImmutableDictionary<DocumentUri, IReadOnlyList<Diagnostic>>> GetAllDiagnostics(CancellationToken? cancellationToken = null) {
    cancellationToken ??= CancellationToken;

    foreach (var entry in Projects.Managers) {
      try {
        await entry.GetLastDocumentAsync().WaitAsync(cancellationToken.Value);
      } catch (TaskCanceledException) {

      }
    }

    var verificationDocumentItem = CreateTestDocument("class X {does not parse", $"AssertNoDiagnosticsAreComing{fileIndex++}.dfy");
    await client.OpenDocumentAndWaitAsync(verificationDocumentItem, cancellationToken.Value);

    var result = ImmutableDictionary<DocumentUri, IReadOnlyList<Diagnostic>>.Empty;
    while (true) {
      var resolutionReport = await diagnosticsReceiver.AwaitNextNotificationAsync(cancellationToken.Value);
      if (verificationDocumentItem.Uri.Equals(resolutionReport.Uri)) {
        break;
      }

      result = result.Add(resolutionReport.Uri, resolutionReport.Diagnostics.ToList());
    }
    client.DidCloseTextDocument(new DidCloseTextDocumentParams {
      TextDocument = verificationDocumentItem
    });
    var hideReport = await diagnosticsReceiver.AwaitNextNotificationAsync(cancellationToken.Value);
    AssertM.Equal(verificationDocumentItem.Uri, hideReport.Uri,
      "2) Unexpected diagnostics were received whereas none were expected:\n" +
      string.Join(",", hideReport.Diagnostics.Select(diagnostic => diagnostic.ToString())));
    return result;
  }

  protected async Task<FileVerificationStatus> WaitUntilAllStatusAreCompleted(TextDocumentItem documentId,
    CancellationToken? cancellationToken = null,
    bool allowStale = false) {
    cancellationToken ??= CancellationToken;

    CompilationStatusParams compilationStatusParams = compilationStatusReceiver.GetLast(s => s.Uri == documentId.Uri);
    while (compilationStatusParams == null || compilationStatusParams.Version != documentId.Version || compilationStatusParams.Uri != documentId.Uri ||
           compilationStatusParams.Status is CompilationStatus.Parsing or CompilationStatus.ResolutionStarted) {
      compilationStatusParams = await compilationStatusReceiver.AwaitNextNotificationAsync(cancellationToken.Value);
    }

    if (compilationStatusParams.Status != CompilationStatus.ResolutionSucceeded) {
      return null;
    }
    var fileVerificationStatus = verificationStatusReceiver.GetLast(v => v.Uri == documentId.Uri);
    if (fileVerificationStatus != null) {
      while (fileVerificationStatus.NamedVerifiables.Any(method => !(allowStale && method.Status == PublishedVerificationStatus.Stale) && method.Status < PublishedVerificationStatus.Error)) {
        fileVerificationStatus = await verificationStatusReceiver.AwaitNextNotificationAsync(cancellationToken.Value);

      }
    }

    return fileVerificationStatus;
  }

  public async Task<PublishDiagnosticsParams> GetLastDiagnosticsParams(TextDocumentItem documentItem, CancellationToken cancellationToken, bool allowStale = false) {
    var status = await WaitUntilAllStatusAreCompleted(documentItem, cancellationToken, allowStale);
    await Task.Delay(10);
    var result = diagnosticsReceiver.History.Last(d => d.Uri == documentItem.Uri);
    diagnosticsReceiver.ClearQueue();
    return result;
  }

  public async Task<Diagnostic[]> GetLastDiagnostics(TextDocumentItem documentItem, CancellationToken? cancellationToken = null, bool allowStale = false) {
    var paramsResult = await GetLastDiagnosticsParams(documentItem, cancellationToken ?? CancellationToken, allowStale);
    return paramsResult.Diagnostics.ToArray();
  }

  public virtual Task InitializeAsync() {
    return SetUp(null);
  }

  public Task DisposeAsync() {
    return client.Shutdown();
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

  public record Change(Range range, String inserted);

  public record Changes(List<Change> changes);

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

  protected void ApplyChanges(ref TextDocumentItem documentItem, List<Change> changes) {
    documentItem = documentItem with { Version = documentItem.Version + 1 };
    client.DidChangeTextDocument(new DidChangeTextDocumentParams {
      TextDocument = new OptionalVersionedTextDocumentIdentifier {
        Uri = documentItem.Uri,
        Version = documentItem.Version
      },
      ContentChanges =
        changes.Select(change =>
          new TextDocumentContentChangeEvent {
            Range = change.range,
            Text = change.inserted
          }).ToArray()
    });
  }

  public async Task AssertNoVerificationStatusIsComing(TextDocumentItem documentItem, CancellationToken cancellationToken) {
    foreach (var entry in Projects.Managers) {
      try {
        await entry.GetLastDocumentAsync().WaitAsync(cancellationToken);
      } catch (TaskCanceledException) {

      }
    }
    var verificationDocumentItem = CreateTestDocument("method Foo() { assert false; }", $"verification{fileIndex++}.dfy");
    await client.OpenDocumentAndWaitAsync(verificationDocumentItem, cancellationToken);
    var statusReport = await verificationStatusReceiver.AwaitNextNotificationAsync(cancellationToken);
    try {
      Assert.Equal(verificationDocumentItem.Uri, statusReport.Uri);
    } catch (AssertActualExpectedException) {
      await output.WriteLineAsync($"StatusReport: {statusReport.Stringify()}");
    }
    client.DidCloseTextDocument(new DidCloseTextDocumentParams {
      TextDocument = verificationDocumentItem
    });
    var emptyReport = await verificationStatusReceiver.AwaitNextNotificationAsync(cancellationToken);
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

  public async Task AssertNoDiagnosticsAreComing(CancellationToken cancellationToken, TextDocumentItem forDocument = null, bool waitFirst = false) {

    var verificationDocumentItem = CreateTestDocument("class X {does not parse", $"AssertNoDiagnosticsAreComing{fileIndex++}.dfy");
    await client.OpenDocumentAndWaitAsync(verificationDocumentItem, cancellationToken);

    while (true) {
      var resolutionReport = await diagnosticsReceiver.AwaitNextNotificationAsync(cancellationToken);
      if (verificationDocumentItem.Uri.Equals(resolutionReport.Uri)) {
        break;
      }

      if (forDocument != null && !forDocument.Uri.Equals(resolutionReport.Uri)) {
        continue;
      }

      AssertM.Equal(verificationDocumentItem.Uri, resolutionReport.Uri,
        "1) Unexpected diagnostics were received whereas none were expected:\n" +
        string.Join(",", resolutionReport.Diagnostics.Select(diagnostic => diagnostic.ToString())));
    }
    client.DidCloseTextDocument(new DidCloseTextDocumentParams {
      TextDocument = verificationDocumentItem
    });
    var hideReport = await diagnosticsReceiver.AwaitNextNotificationAsync(cancellationToken);
    AssertM.Equal(verificationDocumentItem.Uri, hideReport.Uri,
      "2) Unexpected diagnostics were received whereas none were expected:\n" +
      string.Join(",", hideReport.Diagnostics.Select(diagnostic => diagnostic.ToString())));
  }

  protected async Task AssertNoResolutionErrors(TextDocumentItem documentItem) {
    var resolutionDiagnostics = (await Projects.GetResolvedDocumentAsyncNormalizeUri(documentItem))!.GetDiagnosticsForUri(documentItem.Uri.ToUri()).ToList();
    // A document without diagnostics may be absent, even if resolved successfully
    var resolutionErrors = resolutionDiagnostics.Where(d => d.Severity == DiagnosticSeverity.Error);
    if (resolutionErrors.Any()) {
      Assert.Fail($"Found resolution errors: {resolutionErrors.Stringify()}");
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

  protected async Task<TextDocumentItem> GetDocumentItem(string source, string filename, bool includeProjectFile) {
    var directory = Path.Combine(Path.GetTempPath(), Path.GetRandomFileName());
    source = source.TrimStart();
    if (includeProjectFile) {
      var projectFile = CreateTestDocument("", Path.Combine(directory, DafnyProject.FileName));
      await client.OpenDocumentAndWaitAsync(projectFile, CancellationToken);
    }
    var documentItem = CreateTestDocument(source, Path.Combine(directory, filename));
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
    var document = await Projects.GetLastDocumentAsync(documentItem);
    Assert.NotNull(document);
    return documentItem;
  }
}