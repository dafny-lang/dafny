using MediatR;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Client.Capabilities;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using OmniSharp.Extensions.LanguageServer.Protocol.Server.Capabilities;
using System;
using System.Collections.Generic;
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
  /// The documents are managed using an implementation of <see cref="IProjectDatabase"/>.
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
    private readonly IProjectDatabase projects;
    private readonly ITelemetryPublisher telemetryPublisher;
    private readonly INotificationPublisher notificationPublisher;

    public DafnyTextDocumentHandler(
      ILogger<DafnyTextDocumentHandler> logger, IProjectDatabase projects,
      ITelemetryPublisher telemetryPublisher, INotificationPublisher notificationPublisher
    ) {
      this.logger = logger;
      this.projects = projects;
      this.telemetryPublisher = telemetryPublisher;
      this.notificationPublisher = notificationPublisher;
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

    public override async Task<Unit> Handle(DidOpenTextDocumentParams notification, CancellationToken cancellationToken) {
      logger.LogDebug("received open notification {DocumentUri}", notification.TextDocument.Uri);
      try {
        await projects.OpenDocument(new DocumentTextBuffer(notification.TextDocument));
      } catch (Exception e) {
        telemetryPublisher.PublishUnhandledException(e);
      }

      logger.LogDebug($"Finished opening document {notification.TextDocument.Uri}");
      return Unit.Value;
    }

    /// <summary>
    /// Can be called in parallel
    /// </summary>
    public override async Task<Unit> Handle(DidCloseTextDocumentParams notification, CancellationToken cancellationToken) {
      logger.LogDebug("received close notification {DocumentUri}", notification.TextDocument.Uri);
      try {
        await projects.CloseDocumentAsync(notification.TextDocument);
      } catch (Exception e) {
        telemetryPublisher.PublishUnhandledException(e);
      }
      return Unit.Value;
    }

    public override async Task<Unit> Handle(DidChangeTextDocumentParams notification, CancellationToken cancellationToken) {
      logger.LogDebug($"Received change notification {notification.TextDocument.Uri} version {notification.TextDocument.Version}");
      try {
        await projects.UpdateDocument(notification);
      } catch (Exception e) {
        telemetryPublisher.PublishUnhandledException(e);
      }
      return Unit.Value;
    }

    public override Task<Unit> Handle(DidSaveTextDocumentParams notification, CancellationToken cancellationToken) {
      logger.LogDebug("received save notification {DocumentUri}", notification.TextDocument.Uri);
      try {
        projects.SaveDocument(notification.TextDocument);
      } catch (Exception e) {
        telemetryPublisher.PublishUnhandledException(e);
      }

      return Unit.Task;
    }
  }
}
