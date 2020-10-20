using DafnyLS.Language;
using DafnyLS.Workspace;
using MediatR;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Client.Capabilities;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using OmniSharp.Extensions.LanguageServer.Protocol.Server.Capabilities;
using System.Threading;
using System.Threading.Tasks;

namespace DafnyLS.Handlers {
  /// <summary>
  /// LSP Synchronization handler for document based events, such as change, open, close and save.
  /// The documents are managed using an implementaiton of <see cref="IDocumentDatabase"/>.
  /// </summary>
  public class DafnyTextDocumentHandler : ITextDocumentSyncHandler {
    private readonly ILogger _logger;
    private readonly IDocumentDatabase _documents;
    private readonly IDiagnosticPublisher _diagnosticPublisher;

    private const string LanguageId = "dafny";

    private readonly DocumentSelector _documentSelector = new DocumentSelector(
      new DocumentFilter { Pattern = "**/*.dfy" }
    );

    public DafnyTextDocumentHandler(ILogger<DafnyTextDocumentHandler> logger, IDocumentDatabase documents, IDiagnosticPublisher diagnosticPublisher) {
      _logger = logger;
      _documents = documents;
      _diagnosticPublisher = diagnosticPublisher;
    }

    public TextDocumentAttributes GetTextDocumentAttributes(DocumentUri uri) {
      return new TextDocumentAttributes(uri, LanguageId);
    }

    public void SetCapability(SynchronizationCapability capability) {
      // TODO
    }

    TextDocumentRegistrationOptions IRegistration<TextDocumentRegistrationOptions>.GetRegistrationOptions() {
      return new TextDocumentRegistrationOptions {
        DocumentSelector = _documentSelector
      };
    }

    public async Task<Unit> Handle(DidOpenTextDocumentParams notification, CancellationToken cancellationToken) {
      _logger.LogTrace("received open notification {}", notification.TextDocument.Uri);
      var document = await _documents.LoadDocumentAsync(notification.TextDocument, cancellationToken);
      _diagnosticPublisher.PublishDiagnostics(document, cancellationToken);
      return Unit.Value;
    }

    public Task<Unit> Handle(DidCloseTextDocumentParams notification, CancellationToken cancellationToken) {
      _logger.LogTrace("received close notification {}", notification.TextDocument.Uri);
      _documents.CloseDocument(notification.TextDocument);
      return Unit.Task;
    }

    TextDocumentChangeRegistrationOptions IRegistration<TextDocumentChangeRegistrationOptions>.GetRegistrationOptions() {
      return new TextDocumentChangeRegistrationOptions() {
        DocumentSelector = _documentSelector,
        SyncKind = TextDocumentSyncKind.Full
      };
    }

    public async Task<Unit> Handle(DidChangeTextDocumentParams notification, CancellationToken cancellationToken) {
      _logger.LogTrace("received change notification {}", notification.TextDocument.Uri);
      var document = await _documents.UpdateDocumentAsync(notification, cancellationToken);
      if(document != null) {
        _diagnosticPublisher.PublishDiagnostics(document, cancellationToken);
      }
      return Unit.Value;
    }

    TextDocumentSaveRegistrationOptions IRegistration<TextDocumentSaveRegistrationOptions>.GetRegistrationOptions() {
      return new TextDocumentSaveRegistrationOptions {
        DocumentSelector = _documentSelector,
        IncludeText = true
      };
    }

    public Task<Unit> Handle(DidSaveTextDocumentParams notification, CancellationToken cancellationToken) {
      _logger.LogTrace("received save notification {}", notification.TextDocument.Uri);
      return Unit.Task;
    }
  }
}
