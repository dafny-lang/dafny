using System;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Extensions.Logging;

namespace Microsoft.Dafny.LanguageServer.Workspace;

class RequestUpdatesOnUriObserver : IObserver<IObservable<DafnyDocument>>, IDisposable {
  private readonly MergeOrdered<DafnyDocument> mergeOrdered;
  private readonly IDisposable subscription;
  private readonly DiagnosticsObserver observer;

  public DafnyDocument PreviouslyPublishedDocument => observer.PreviouslyPublishedDocument;

  public RequestUpdatesOnUriObserver(
    ILogger logger,
    ITelemetryPublisher telemetryPublisher,
    INotificationPublisher notificationPublisher,
    ITextDocumentLoader loader,
    DocumentTextBuffer document) {

    mergeOrdered = new MergeOrdered<DafnyDocument>();
    observer = new DiagnosticsObserver(logger, telemetryPublisher, notificationPublisher, loader, document);
    subscription = mergeOrdered.Subscribe(observer);
  }

  public IObservable<bool> IdleChangesIncludingLast => mergeOrdered.IdleChangesIncludingLast;

  public void Dispose() {
    subscription.Dispose();
  }

  public void OnCompleted() {
    mergeOrdered.OnCompleted();
  }

  public void OnError(Exception error) {
    mergeOrdered.OnError(error);
  }

  public void OnNext(IObservable<DafnyDocument> value) {
    mergeOrdered.OnNext(value);
  }
}

class DiagnosticsObserver : IObserver<DafnyDocument> {
  private readonly ILogger logger;
  private readonly ITelemetryPublisher telemetryPublisher;
  private readonly INotificationPublisher notificationPublisher;
  public DafnyDocument PreviouslyPublishedDocument { get; private set; }

  public DiagnosticsObserver(ILogger logger,
    ITelemetryPublisher telemetryPublisher,
    INotificationPublisher notificationPublisher,
    ITextDocumentLoader loader,
    DocumentTextBuffer document) {
    PreviouslyPublishedDocument = loader.CreateUnloaded(document, CancellationToken.None);
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
    notificationPublisher.PublishNotifications(PreviouslyPublishedDocument, document);
    PreviouslyPublishedDocument = document;
  }
}