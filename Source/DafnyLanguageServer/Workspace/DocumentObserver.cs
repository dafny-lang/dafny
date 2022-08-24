
using System;
using System.Linq;
using System.Threading;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.Workspace;

class DocumentObserver : IObserver<CompilationView> {
  private readonly ILogger logger;
  private readonly ITelemetryPublisher telemetryPublisher;
  private readonly INotificationPublisher notificationPublisher;

  public CompilationView LastPublishedDocument {
    get; private set;
  }

  public DocumentObserver(ILogger logger,
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

  public void OnError(Exception exception) {
    if (exception is OperationCanceledException) {
      logger.LogInformation("document processing cancelled.");
      return;
    }

    var previousDiagnostics = LastPublishedDocument.LoadCanceled
      ? new Diagnostic[] { }
      : LastPublishedDocument.ResolutionDiagnostics;
    var internalErrorDiagnostic = new Diagnostic {
      Message =
        "Dafny encountered an internal error. Please report it at <https://github.com/dafny-lang/dafny/issues>.\n" +
        exception,
      Severity = DiagnosticSeverity.Error,
      Range = new Range(0, 0, 0, 1)
    };
    var documentToPublish = LastPublishedDocument with {
      LoadCanceled = false,
      ResolutionDiagnostics = previousDiagnostics.Concat(new[] { internalErrorDiagnostic }).ToList()
    };

    OnNext(documentToPublish);

    logger.LogError(exception, "error while handling document event");
    telemetryPublisher.PublishUnhandledException(exception);
  }

  private readonly object lastPublishedDocumentLock = new();
  public void OnNext(CompilationView view) {
    lock (lastPublishedDocumentLock) {
      if (view.Version < LastPublishedDocument.Version) {
        return;
      }

      notificationPublisher.PublishNotifications(LastPublishedDocument, view);
      LastPublishedDocument = view; // Snapshot before storing.
    }
  }
}