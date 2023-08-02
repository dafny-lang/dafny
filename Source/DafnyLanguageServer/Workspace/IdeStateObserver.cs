
using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using System.Threading;
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
    var ideState = loader.CreateUnloaded(compilation) with { Compilation = new Compilation(LastPublishedState.Version + 1, LastPublishedState.Compilation.Project, compilation.RootUris) };
    notificationPublisher.PublishNotifications(LastPublishedState, ideState);
    telemetryPublisher.PublishUpdateComplete();
  }

  public void OnError(Exception exception) {
    if (exception is OperationCanceledException) {
      logger.LogInformation("document processing cancelled.");
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
    logger.LogTrace($"IdeStateObserver.OnNext entered, threadId: {Thread.CurrentThread.ManagedThreadId}");
    lock (lastPublishedStateLock) {
      if (snapshot.Version < LastPublishedState.Version) {
        return;
      }

      notificationPublisher.PublishNotifications(LastPublishedState, snapshot);
      LastPublishedState = snapshot;
    }
  }

  public void Migrate(DidChangeTextDocumentParams documentChange) {

    var migratedVerificationTrees = LastPublishedState.VerificationTrees.ToDictionary(
      kv => kv.Key, kv =>
        relocator.RelocateVerificationTree(kv.Value, documentChange, CancellationToken.None));
    LastPublishedState = LastPublishedState with {
      ImplementationViews = MigrateImplementationViews(documentChange, LastPublishedState.ImplementationViews),
      SignatureAndCompletionTable = relocator.RelocateSymbols(LastPublishedState.SignatureAndCompletionTable,
        documentChange, CancellationToken.None),
      VerificationTrees = migratedVerificationTrees
    };
  }

  private Dictionary<Location, Dictionary<string, IdeImplementationView>> MigrateImplementationViews(DidChangeTextDocumentParams documentChange,
      Dictionary<Location, Dictionary<string, IdeImplementationView>> oldVerificationDiagnostics) {
    var result = new Dictionary<Location, Dictionary<string, IdeImplementationView>>();
    foreach (var entry in oldVerificationDiagnostics) {
      var newOuterRange = relocator.RelocateRange(entry.Key.Range, documentChange, CancellationToken.None);
      if (newOuterRange == null) {
        continue;
      }

      var newValue = new Dictionary<string, IdeImplementationView>();
      foreach (var innerEntry in entry.Value) {
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
      }, newValue);
    }
    return result;
  }
}
