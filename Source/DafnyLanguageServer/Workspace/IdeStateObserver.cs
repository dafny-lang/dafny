
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

  public void ClearState() {
    var ideState = initialState with {
      Input = initialState.Input with { Version = initialState.Version + 1 }
    };
    logger.LogInformation($"IdeStateObserver ClearState called, publishing version ${ideState.Version} for uri {ideState.Uri}");
    notificationPublisher.PublishNotifications(LastPublishedState, ideState);
    telemetryPublisher.PublishUpdateComplete();
  }

  public void OnCompleted() {
    var ideState = initialState with {
      Input = initialState.Input with { Version = initialState.Version + 1 }
    };
    logger.LogInformation($"IdeStateObserver OnCompleted called, publishing version ${ideState.Version} for uri {ideState.Uri}");
    notificationPublisher.PublishNotifications(LastPublishedState, ideState);
    telemetryPublisher.PublishUpdateComplete();
  }

  public void OnError(Exception exception) {
  }

  public void OnNext(IdeState snapshot) {
    lock (lastPublishedStateLock) {
      if (snapshot.Version < LastPublishedState.Version) {
        logger.LogInformation($"Skipping PublishNotifications because snapshot with status {snapshot.Status} was version {snapshot.Version} and last published version was {LastPublishedState.Version}");
        return;
      }

      notificationPublisher.PublishNotifications(LastPublishedState, snapshot);
      logger.LogInformation($"Updating LastPublishedState to version {snapshot.Version}, uri {LastPublishedState.Input.Uri.ToUri()}");
      LastPublishedState = snapshot;
    }
  }

  public void Migrate(DafnyOptions options, Migrator migrator, int version) {
    lock (lastPublishedStateLock) {
      logger.LogInformation($"Migrating LastPublishedState to version {version}, uri {LastPublishedState.Input.Uri.ToUri()}");
      LastPublishedState = LastPublishedState.Migrate(options, migrator, version, true);
    }
  }
}
