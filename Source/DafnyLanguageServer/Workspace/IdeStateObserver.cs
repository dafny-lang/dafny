
using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using System.Threading;
using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.Workspace.ChangeProcessors;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.Workspace;

public delegate IdeStateObserver CreateIdeStateObserver(Compilation compilation);

public class IdeStateObserver : IObserver<IdeState> {
  private readonly ILogger logger;
  private readonly ITelemetryPublisher telemetryPublisher;
  private readonly INotificationPublisher notificationPublisher;
  private readonly ITextDocumentLoader loader;
  private readonly IRelocator relocator;
  private readonly Compilation compilation;

  private readonly object lastPublishedStateLock = new();

  public IdeState LastPublishedState { get; private set; }

  public IdeStateObserver(ILogger logger,
    ITelemetryPublisher telemetryPublisher,
    INotificationPublisher notificationPublisher,
    ITextDocumentLoader loader,
    IRelocator relocator,
    Compilation compilation) {
    LastPublishedState = loader.CreateUnloaded(compilation);
    this.logger = logger;
    this.telemetryPublisher = telemetryPublisher;
    this.notificationPublisher = notificationPublisher;
    this.loader = loader;
    this.compilation = compilation;
    this.relocator = relocator;
  }

  public void OnCompleted() {
    var initialCompilation = new Compilation(LastPublishedState.Version + 1, LastPublishedState.Compilation.Project, compilation.RootUris);
    var ideState = loader.CreateUnloaded(initialCompilation);
#pragma warning disable VSTHRD002
    notificationPublisher.PublishNotifications(LastPublishedState, ideState).Wait();
#pragma warning restore VSTHRD002
    telemetryPublisher.PublishUpdateComplete();
  }

  public void OnError(Exception exception) {
    if (exception is OperationCanceledException) {
      logger.LogDebug("document processing cancelled.");
      return;
    }

    var internalErrorDiagnostic = new Diagnostic {
      Message =
        "Dafny encountered an internal error. Please report it at <https://github.com/dafny-lang/dafny/issues>.\n" +
        exception,
      Severity = DiagnosticSeverity.Error,
      Range = new Range(0, 0, 0, 1)
    };
    var documentToPublish = LastPublishedState with {
      ResolutionDiagnostics = ImmutableDictionary<Uri, IReadOnlyList<Diagnostic>>.Empty.Add(compilation.Project.Uri, new[] { internalErrorDiagnostic })
    };

    OnNext(documentToPublish);

    logger.LogError(exception, "error while handling document event");
    telemetryPublisher.PublishUnhandledException(exception);
  }

  public void OnNext(IdeState snapshot) {
    lock (lastPublishedStateLock) {
      if (snapshot.Version < LastPublishedState.Version) {
        return;
      }

      // To prevent older updates from being sent after newer ones, we can only run one PublishNotifications at a time.
      // So we wait for it here to finish, and the lock in this method prevents more than one from running at a time.
#pragma warning disable VSTHRD002
      notificationPublisher.PublishNotifications(LastPublishedState, snapshot).Wait();
#pragma warning restore VSTHRD002
      LastPublishedState = snapshot;
      logger.LogDebug($"Updated LastPublishedState to version {snapshot.Version}, uri {compilation.Uri}");
    }
  }

  public void Migrate(DidChangeTextDocumentParams documentChange, int version) {
    lock (lastPublishedStateLock) {
      var migratedVerificationTrees = LastPublishedState.VerificationTrees.ToDictionary(
        kv => kv.Key, kv =>
          relocator.RelocateVerificationTree(kv.Value, documentChange, CancellationToken.None));
      LastPublishedState = LastPublishedState with {
        Version = version,
        VerificationResults = MigrateImplementationViews(documentChange, LastPublishedState.VerificationResults),
        SignatureAndCompletionTable = relocator.RelocateSymbols(LastPublishedState.SignatureAndCompletionTable,
          documentChange, CancellationToken.None),
        VerificationTrees = migratedVerificationTrees
      };
      logger.LogDebug($"Migrated LastPublishedState to version {version}, uri {compilation.Uri}");
    }
  }

  private Dictionary<Location, IdeVerificationResult> MigrateImplementationViews(DidChangeTextDocumentParams documentChange,
      Dictionary<Location, IdeVerificationResult> oldVerificationDiagnostics) {
    var result = new Dictionary<Location, IdeVerificationResult>();
    foreach (var entry in oldVerificationDiagnostics) {
      var newOuterRange = relocator.RelocateRange(entry.Key.Range, documentChange, CancellationToken.None);
      if (newOuterRange == null) {
        continue;
      }

      var newValue = new Dictionary<string, IdeImplementationView>();
      foreach (var innerEntry in entry.Value.Implementations) {
        var newInnerRange = relocator.RelocateRange(innerEntry.Value.Range, documentChange, CancellationToken.None);
        if (newInnerRange != null) {
          newValue.Add(innerEntry.Key, innerEntry.Value with {
            Range = newInnerRange,
            Diagnostics = relocator.RelocateDiagnostics(innerEntry.Value.Diagnostics, documentChange, CancellationToken.None)
          });
        }
      }
      result.Add(new Location() {
        Uri = entry.Key.Uri,
        Range = newOuterRange
      }, entry.Value with { Implementations = newValue });
    }
    return result;
  }
}
