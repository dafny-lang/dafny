using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using System.Reactive.Linq;
using System.Reactive.Subjects;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny.LanguageServer.Workspace;

class DocumentObserver : IObserver<DafnyDocument> {
  private readonly ILogger logger;
  private readonly ITelemetryPublisher telemetryPublisher;
  private readonly INotificationPublisher notificationPublisher;

  public DafnyDocument LastPublishedDocument {
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
      : LastPublishedDocument.ParseAndResolutionDiagnostics;
    var internalErrorDiagnostic = new Diagnostic {
      Message =
        "Dafny encountered an internal error. Please report it at <https://github.com/dafny-lang/dafny/issues>.\n" +
        exception,
      Severity = DiagnosticSeverity.Error,
      Range = LastPublishedDocument.Program.GetFirstTopLevelToken().GetLspRange()
    };
    var documentToPublish = LastPublishedDocument with {
      LoadCanceled = false,
      ParseAndResolutionDiagnostics = previousDiagnostics.Concat(new[] { internalErrorDiagnostic }).ToList()
    };

    OnNext(documentToPublish);

    logger.LogError(exception, "error while handling document event");
    telemetryPublisher.PublishUnhandledException(exception);
  }

  private readonly object lastPublishedDocumentLock = new();
  public void OnNext(DafnyDocument document) {
    lock (lastPublishedDocumentLock) {
      if (document.Version < LastPublishedDocument.Version) {
        return;
      }

      notificationPublisher.PublishNotifications(LastPublishedDocument, document);
      LastPublishedDocument = document.Snapshot(); // Snapshot before storing.
    }
  }
}