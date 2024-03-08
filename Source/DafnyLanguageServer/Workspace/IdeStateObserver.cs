
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
  private readonly TelemetryPublisherBase telemetryPublisher;
  private readonly INotificationPublisher notificationPublisher;

  private readonly object lastPublishedStateLock = new();
  private readonly IdeState initialState;

  public IdeState LastPublishedState { get; private set; }

  public IdeStateObserver(ILogger logger,
    TelemetryPublisherBase telemetryPublisher,
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
    notificationPublisher.PublishNotifications(LastPublishedState, ideState);
    telemetryPublisher.PublishUpdateComplete();
  }

  public void OnError(Exception exception) {
  }

  public void OnNext(IdeState snapshot) {
    lock (lastPublishedStateLock) {
      if (snapshot.Version < LastPublishedState.Version) {
        return;
      }

      notificationPublisher.PublishNotifications(LastPublishedState, snapshot);
      LastPublishedState = snapshot;
      logger.LogDebug($"Updated LastPublishedState to version {snapshot.Version}, uri {initialState.Input.Uri.ToUri()}");
    }
  }

  public void Migrate(DafnyOptions options, Migrator migrator, int version) {
    lock (lastPublishedStateLock) {
      LastPublishedState = LastPublishedState.Migrate(options, migrator, version, true);
      logger.LogDebug($"Migrated LastPublishedState to version {version}, uri {initialState.Input.Uri.ToUri()}");
    }
  }
}
