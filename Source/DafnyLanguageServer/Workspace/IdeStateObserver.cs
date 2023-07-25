
using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using System.Threading;
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
  private readonly Compilation compilation;

  private readonly object lastPublishedStateLock = new();

  public IdeState LastPublishedState { get; private set; }

  public IdeStateObserver(ILogger logger,
    ITelemetryPublisher telemetryPublisher,
    INotificationPublisher notificationPublisher,
    ITextDocumentLoader loader,
    Compilation compilation) {
    LastPublishedState = loader.CreateUnloaded(compilation);
    this.logger = logger;
    this.telemetryPublisher = telemetryPublisher;
    this.notificationPublisher = notificationPublisher;
    this.loader = loader;
    this.compilation = compilation;
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
}
