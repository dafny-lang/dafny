using System;
using System.Collections.Immutable;
using System.Reactive.Linq;
using System.Reactive.Subjects;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Extensions.Logging;

namespace Microsoft.Dafny.LanguageServer.Workspace;

class DiagnosticsObserver : IObserver<DafnyDocument> {
  private readonly ILogger logger;
  private readonly ITelemetryPublisher telemetryPublisher;
  private readonly INotificationPublisher notificationPublisher;

  public DafnyDocument LastPublishedDocument {
    get; private set;

  }

  private readonly ReplaySubject<DafnyDocument> lastAndUpcomingPublishedDocuments = new(1);
  public IObservable<DafnyDocument> LastAndUpcomingPublishedDocuments => lastAndUpcomingPublishedDocuments;

  public DiagnosticsObserver(ILogger logger,
    ITelemetryPublisher telemetryPublisher,
    INotificationPublisher notificationPublisher,
    ITextDocumentLoader loader,
    DocumentTextBuffer document) {
    LastPublishedDocument = loader.CreateUnloaded(document, CancellationToken.None);
    this.logger = logger;
    this.telemetryPublisher = telemetryPublisher;
    this.notificationPublisher = notificationPublisher;
  }

  public void OnCompleted() {
    telemetryPublisher.PublishUpdateComplete();
  }

  public void OnError(Exception e) {
    if (e is TaskCanceledException) {
      OnCompleted();
    } else {
      logger.LogError(e, "error while handling document event");
      telemetryPublisher.PublishUnhandledException(e);
    }
  }

  public void OnNext(DafnyDocument document) {
    notificationPublisher.PublishNotifications(LastPublishedDocument, document);
    LastPublishedDocument = document.Snapshot();
    lastAndUpcomingPublishedDocuments.OnNext(LastPublishedDocument);
  }
}