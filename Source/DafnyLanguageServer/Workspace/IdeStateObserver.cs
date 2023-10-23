
using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Reactive;
using Microsoft.Dafny.LanguageServer.Workspace.ChangeProcessors;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.Workspace;

public delegate IdeStateObserver CreateIdeStateObserver(IdeState initialState);

public class IdeStateObserver : IObserver<IdeState> { // Inheriting from ObserverBase prevents this observer from recovering after a problem
  private readonly ILogger logger;
  private readonly ITelemetryPublisher telemetryPublisher;
  private readonly INotificationPublisher notificationPublisher;

  private readonly object lastPublishedStateLock = new();
  private readonly IdeState initialState;

  public IdeState LastPublishedState { get; private set; }

  public IdeStateObserver(ILogger logger,
    ITelemetryPublisher telemetryPublisher,
    INotificationPublisher notificationPublisher,
    IdeState initialState) {
    this.initialState = initialState;
    LastPublishedState = initialState;
    this.logger = logger;
    this.telemetryPublisher = telemetryPublisher;
    this.notificationPublisher = notificationPublisher;
  }

  public void OnCompleted() {
    var ideState = initialState with {
      Version = LastPublishedState.Version + 1
    };
#pragma warning disable VSTHRD002
    notificationPublisher.PublishNotifications(LastPublishedState, ideState).Wait();
#pragma warning restore VSTHRD002
    telemetryPublisher.PublishUpdateComplete();
  }

  public void OnError(Exception exception) {
    var internalErrorDiagnostic = new Diagnostic {
      Message =
        "Dafny encountered an internal error. Please report it at <https://github.com/dafny-lang/dafny/issues>.\n" +
        exception,
      Severity = DiagnosticSeverity.Error,
      Range = new Range(0, 0, 0, 1)
    };
    var documentToPublish = LastPublishedState with {
      ResolutionDiagnostics = ImmutableDictionary<Uri, IReadOnlyList<Diagnostic>>.Empty.Add(initialState.Compilation.Uri.ToUri(), new[] { internalErrorDiagnostic })
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
      logger.LogDebug($"Updated LastPublishedState to version {snapshot.Version}, uri {initialState.Compilation.Uri.ToUri()}");
    }
  }

  public void Migrate(Migrator migrator, int version) {
    lock (lastPublishedStateLock) {
      LastPublishedState = LastPublishedState.Migrate(migrator, version);
      logger.LogDebug($"Migrated LastPublishedState to version {version}, uri {initialState.Compilation.Uri.ToUri()}");
    }
  }
}
