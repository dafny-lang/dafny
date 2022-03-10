using MediatR;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Client.Capabilities;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using OmniSharp.Extensions.LanguageServer.Protocol.Server.Capabilities;
using System;
using System.Threading;
using System.Threading.Tasks;

// Justification: The handler must not await document loads. Errors are handled within the observer set up by ForwardDiagnostics.
#pragma warning disable CS4014 // Because this call is not awaited, execution of the current method continues before the call is completed
#pragma warning disable VSTHRD110 // Observe result of async calls

// Justification: The task is launched within the same class
#pragma warning disable VSTHRD003 // Avoid awaiting foreign Tasks

namespace Microsoft.Dafny.LanguageServer.Handlers {
  /// <summary>
  /// LSP Synchronization handler for document based events, such as change, open, close and save.
  /// The documents are managed using an implementation of <see cref="IDocumentDatabase"/>.
  /// </summary>
  /// <remarks>
  /// The <see cref="CancellationToken"/> of all requests is not used here. The reason for this is because document changes are applied in the
  /// background to allow the request to complete immediately. This feature allows new document changes to be received an cancel any
  /// outstanding document changes.
  /// However, the cancellation token is marked as cancelled upon request completion. If it was used for the background processing, it would
  /// break the background processing if used.
  /// </remarks>
  public class DafnyTextDocumentHandler : TextDocumentSyncHandlerBase {
    private const string LanguageId = "dafny";

    private readonly ILogger logger;
    private readonly IDocumentDatabase documents;
    private readonly ITelemetryPublisher telemetryPublisher;
    private readonly IDiagnosticPublisher diagnosticPublisher;

    public DafnyTextDocumentHandler(
      ILogger<DafnyTextDocumentHandler> logger, IDocumentDatabase documents,
      ITelemetryPublisher telemetryPublisher, IDiagnosticPublisher diagnosticPublisher
    ) {
      this.logger = logger;
      this.documents = documents;
      this.telemetryPublisher = telemetryPublisher;
      this.diagnosticPublisher = diagnosticPublisher;
    }

    protected override TextDocumentSyncRegistrationOptions CreateRegistrationOptions(SynchronizationCapability capability, ClientCapabilities clientCapabilities) {
      return new TextDocumentSyncRegistrationOptions {
        DocumentSelector = DocumentSelector.ForLanguage(LanguageId),
        Change = TextDocumentSyncKind.Incremental
      };
    }

    public override TextDocumentAttributes GetTextDocumentAttributes(DocumentUri uri) {
      return new TextDocumentAttributes(uri, LanguageId);
    }

    public override Task<Unit> Handle(DidOpenTextDocumentParams notification, CancellationToken cancellationToken) {
      logger.LogTrace("received open notification {DocumentUri}", notification.TextDocument.Uri);
      ForwardDiagnostics(documents.OpenDocument(notification.TextDocument));
      return Unit.Task;
    }

    public override Task<Unit> Handle(DidCloseTextDocumentParams notification, CancellationToken cancellationToken) {
      logger.LogTrace("received close notification {DocumentUri}", notification.TextDocument.Uri);
      CloseDocumentAndHideDiagnosticsAsync(notification.TextDocument);
      return Unit.Task;
    }

    public override Task<Unit> Handle(DidChangeTextDocumentParams notification, CancellationToken cancellationToken) {
      logger.LogTrace("received change notification {DocumentUri}", notification.TextDocument.Uri);
      ForwardDiagnostics(documents.UpdateDocument(notification));
      return Unit.Task;
    }

    public override Task<Unit> Handle(DidSaveTextDocumentParams notification, CancellationToken cancellationToken) {
      logger.LogTrace("received save notification {DocumentUri}", notification.TextDocument.Uri);
      ForwardDiagnostics(documents.SaveDocument(notification.TextDocument));
      return Unit.Task;
    }

    private void ForwardDiagnostics(IObservable<DafnyDocument> obs) {
      obs.Subscribe(new DiagnosticsObserver(logger, telemetryPublisher, diagnosticPublisher));
    }

    private class DiagnosticsObserver : IObserver<DafnyDocument> {
      private readonly ILogger logger;
      private readonly ITelemetryPublisher telemetryPublisher;
      private readonly IDiagnosticPublisher diagnosticPublisher;

      public DiagnosticsObserver(ILogger logger, ITelemetryPublisher telemetryPublisher, IDiagnosticPublisher diagnosticPublisher) {
        this.logger = logger;
        this.telemetryPublisher = telemetryPublisher;
        this.diagnosticPublisher = diagnosticPublisher;
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
        diagnosticPublisher.PublishDiagnostics(document);
      }
    }

    private async Task CloseDocumentAndHideDiagnosticsAsync(TextDocumentIdentifier documentId) {
      try {
        await documents.CloseDocumentAsync(documentId);
      } catch (Exception e) {
        logger.LogError(e, "error while closing the document");
      }
      diagnosticPublisher.HideDiagnostics(documentId);
    }
  }
}
