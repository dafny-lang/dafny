using MediatR;
using Microsoft.Dafny.LanguageServer.Language;
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

namespace Microsoft.Dafny.LanguageServer.Handlers {
  /// <summary>
  /// LSP Synchronization handler for document based events, such as change, open, close and save.
  /// The documents are managed using an implementaiton of <see cref="IDocumentDatabase"/>.
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

    private readonly ILogger _logger;
    private readonly IDocumentDatabase _documents;
    private readonly IDiagnosticPublisher _diagnosticPublisher;

    public DafnyTextDocumentHandler(
        ILogger<DafnyTextDocumentHandler> logger, IDocumentDatabase documents, IDiagnosticPublisher diagnosticPublisher
    ) {
      _logger = logger;
      _documents = documents;
      _diagnosticPublisher = diagnosticPublisher;
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
      _logger.LogTrace("received open notification {DocumentUri}", notification.TextDocument.Uri);
      _documents.LoadDocumentAsync(notification.TextDocument)
        .ContinueWith(PublishDiagnosticsAsync);
      return Unit.Task;
    }

    public override Task<Unit> Handle(DidCloseTextDocumentParams notification, CancellationToken cancellationToken) {
      _logger.LogTrace("received close notification {DocumentUri}", notification.TextDocument.Uri);
      _documents.CloseDocumentAsync(notification.TextDocument)
        .ContinueWith(_ => _diagnosticPublisher.HideDiagnostics(notification.TextDocument));
      return Unit.Task;
    }

    public override Task<Unit> Handle(DidChangeTextDocumentParams notification, CancellationToken cancellationToken) {
      _logger.LogTrace("received change notification {DocumentUri}", notification.TextDocument.Uri);
      _documents.UpdateDocumentAsync(notification)
        .ContinueWith(PublishDiagnosticsAsync);
      return Unit.Task;
    }

    public override Task<Unit> Handle(DidSaveTextDocumentParams notification, CancellationToken cancellationToken) {
      _logger.LogTrace("received save notification {DocumentUri}", notification.TextDocument.Uri);
      _documents.SaveDocumentAsync(notification.TextDocument)
        .ContinueWith(PublishDiagnosticsAsync);
      return Unit.Task;
    }

    private async Task PublishDiagnosticsAsync(Task<DafnyDocument?> documentTask) {
      try {
        var document = await documentTask;
        if (document != null) {
          _diagnosticPublisher.PublishDiagnostics(document);
        } else {
          _logger.LogWarning("had to publish diagnostics for an unavailable document");
        }
      } catch (Exception e) when (e is not OperationCanceledException) {
        _logger.LogError(e, "error handling document event");
      }
    }
  }
}
