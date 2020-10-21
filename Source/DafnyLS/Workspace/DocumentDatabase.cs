using DafnyLS.Language;
using DafnyLS.Util;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Concurrent;
using System.Diagnostics.CodeAnalysis;
using System.Threading;
using System.Threading.Tasks;

namespace DafnyLS.Workspace {
  /// <summary>
  /// Thread-safe document database implementation.
  /// </summary>
  /// <remarks>
  /// The current implementation only supports full document updates (not deltas).
  /// </remarks>
  public class DocumentDatabase : IDocumentDatabase {
    private readonly ILogger _logger;
    private readonly ConcurrentDictionary<DocumentUri, DafnyDocument> _documents = new ConcurrentDictionary<DocumentUri, DafnyDocument>();
    private readonly ITextDocumentLoader _documentLoader;

    public DocumentDatabase(ILogger<DocumentDatabase> logger, ITextDocumentLoader documentLoader) {
      _logger = logger;
      _documentLoader = documentLoader;
    }

    public async Task<DafnyDocument> LoadDocumentAsync(TextDocumentItem textDocument, CancellationToken cancellationToken) {
      var dafnyDocument = await _documentLoader.LoadAsync(textDocument, cancellationToken);
      var databaseDocument = _documents.AddOrUpdate(textDocument.Uri, dafnyDocument, (uri, old) => dafnyDocument.Version > old.Version ? dafnyDocument : old);
      if (databaseDocument != dafnyDocument) {
        _logger.LogDebug("a newer version of {} was already loaded", textDocument.Uri);
      }
      return databaseDocument;
    }

    public bool CloseDocument(TextDocumentIdentifier documentId) {
      if(!_documents.TryRemove(documentId.Uri, out var _)) {
        _logger.LogTrace("the document {} was already closed", documentId);
        return false;
      }
      return true;
    }
    
    public async Task<DafnyDocument?> UpdateDocumentAsync(DidChangeTextDocumentParams documentChange, CancellationToken cancellationToken) {
      var documentId = documentChange.TextDocument;
      while (_documents.TryGetValue(documentId.Uri, out var oldDocument)) {
        cancellationToken.ThrowIfCancellationRequested();
        if (documentId.Version < oldDocument.Version) {
          _logger.LogDebug("skipping update of {} since the current version is newer (old={} < new={})",
            documentId.Uri, oldDocument.Version, documentId.Version);
          return oldDocument;
        }
        var mergedDocument = await MergeDocumentChangesAsync(oldDocument, documentChange, cancellationToken);
        if (_documents.TryUpdate(documentId.Uri, mergedDocument, oldDocument)) {
          return mergedDocument;
        }
      }
      _logger.LogWarning("received update for untracked document {}", documentId.Uri);
      return null;
    }

    private Task<DafnyDocument> MergeDocumentChangesAsync(DafnyDocument oldDocument, DidChangeTextDocumentParams documentChange, CancellationToken cancellationToken) {
      var mergedItem = new TextDocumentItem {
        LanguageId = oldDocument.Text.LanguageId,
        Uri = oldDocument.Uri,
        Version = documentChange.TextDocument.Version,
        Text = ApplyChanges(oldDocument.Text.Text, documentChange.ContentChanges, cancellationToken)
      };
      // TODO check if dafny could resolve the semantic model. If that's not the case, adapt the current symbol table according to the changes.
      return _documentLoader.LoadAsync(mergedItem, cancellationToken);
    }

    private static string ApplyChanges(string originalText, Container<TextDocumentContentChangeEvent> changes, CancellationToken cancellationToken) {
      var mergedText = originalText;
      foreach(var change in changes) {
        cancellationToken.ThrowIfCancellationRequested();
        mergedText = ApplyChanges(mergedText, change, cancellationToken);
      }
      return mergedText;
    }

    private static string ApplyChanges(string originalText, TextDocumentContentChangeEvent change, CancellationToken cancellationToken) {
      if(change.Range == null) {
        // The property Range is null if a full document change was sent.
        return change.Text;
      }
      int absoluteStart = change.Range.Start.ToAbsolutePosition(originalText, cancellationToken);
      int absoluteEnd = change.Range.End.ToAbsolutePosition(originalText, cancellationToken);
      return originalText[..absoluteStart] + change.Text + originalText[absoluteEnd..];
    }

    public bool TryGetDocument(TextDocumentIdentifier documentId, [NotNullWhen(true)] out DafnyDocument? document) {
      return _documents.TryGetValue(documentId.Uri, out document);
    }
  }
}
