using System;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Extensions.Logging;
using Microsoft.Extensions.Options;
using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Concurrent;
using System.Diagnostics.CodeAnalysis;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Boogie;

namespace Microsoft.Dafny.LanguageServer.Workspace {
  /// <summary>
  /// Thread-safe document database implementation.
  /// </summary>
  /// <remarks>
  /// The current implementation only supports full document updates (not deltas).
  /// </remarks>
  public class DocumentDatabase : IDocumentDatabase {
    private readonly ILogger _logger;
    private readonly DocumentOptions _options;
    private readonly ConcurrentDictionary<DocumentUri, DafnyDocument> _documents = new();
    private readonly ITextDocumentLoader _documentLoader;
    private readonly IDocumentUpdater _documentUpdater;

    private bool VerifyOnLoad => _options.Verify == AutoVerification.OnChange;
    private bool VerifyOnSave => _options.Verify == AutoVerification.OnSave;

    private string[] ProverOptions =>
      _options.ProverOptions.Split(new[] { " ", "\n", "\t" },
        StringSplitOptions.RemoveEmptyEntries);

    public DocumentDatabase(
      ILogger<DocumentDatabase> logger,
      IOptions<DocumentOptions> options,
      ITextDocumentLoader documentLoader,
      IDocumentUpdater documentUpdater
    ) {
      _logger = logger;
      _options = options.Value;
      _documentLoader = documentLoader;
      _documentUpdater = documentUpdater;
      CommandLineOptions.Clo.ProverOptions = ProverOptions.ToList();
    }

    public async Task<DafnyDocument> LoadDocumentAsync(TextDocumentItem textDocument, CancellationToken cancellationToken) {
      var dafnyDocument = await _documentLoader.LoadAsync(textDocument, VerifyOnLoad, cancellationToken);
      var databaseDocument = _documents.AddOrUpdate(textDocument.Uri, dafnyDocument, (uri, old) => dafnyDocument.Version > old.Version ? dafnyDocument : old);
      if (databaseDocument != dafnyDocument) {
        _logger.LogDebug("a newer version of {DocumentUri} was already loaded", textDocument.Uri);
      }
      return databaseDocument;
    }

    public DafnyDocument? CloseDocument(TextDocumentIdentifier documentId) {
      DafnyDocument? document;
      if (!_documents.TryRemove(documentId.Uri, out document)) {
        _logger.LogTrace("the document {DocumentId} was already closed", documentId);
        return null;
      }
      return document;
    }

    // TODO refresh loaded documents that depend on this document? Maybe at least when saving?
    public async Task<DafnyDocument?> UpdateDocumentAsync(DidChangeTextDocumentParams documentChange, CancellationToken cancellationToken) {
      var documentId = documentChange.TextDocument;
      while (_documents.TryGetValue(documentId.Uri, out var oldDocument)) {
        cancellationToken.ThrowIfCancellationRequested();
        if (documentId.Version < oldDocument.Version) {
          _logger.LogDebug("skipping update of {DocumentUri} since the current version is newer (old={OldVersion} > new={NewVersion})",
            documentId.Uri, oldDocument.Version, documentId.Version);
          return oldDocument;
        }
        var mergedDocument = await _documentUpdater.ApplyChangesAsync(oldDocument, documentChange, cancellationToken);
        if (_documents.TryUpdate(documentId.Uri, mergedDocument, oldDocument)) {
          return mergedDocument;
        }
      }
      _logger.LogWarning("received update for untracked document {DocumentUri}", documentId.Uri);
      return null;
    }

    public async Task<DafnyDocument?> SaveDocumentAsync(TextDocumentIdentifier documentId, CancellationToken cancellationToken) {
      if (VerifyOnSave) {
        return await VerifyDocumentAsync(documentId, cancellationToken);
      }
      if (_documents.TryGetValue(documentId.Uri, out var document)) {
        return document;
      }
      return null;
    }

    public async Task<DafnyDocument?> VerifyDocumentAsync(TextDocumentIdentifier documentId, CancellationToken cancellationToken) {
      while (_documents.TryGetValue(documentId.Uri, out var oldDocument)) {
        cancellationToken.ThrowIfCancellationRequested();
        var verifiedDocument = await _documentLoader.LoadAsync(oldDocument.Text, true, cancellationToken);
        // We do not update the document if the symbol resolution failed. Otherwise we'd lose
        // the previous semantic model migrations.
        var newDocument = verifiedDocument.SymbolTable.Resolved ? verifiedDocument : oldDocument;
        if (_documents.TryUpdate(documentId.Uri, newDocument, oldDocument)) {
          return newDocument;
        }
      }
      return null;
    }

    public bool TryGetDocument(TextDocumentIdentifier documentId, [NotNullWhen(true)] out DafnyDocument? document) {
      return _documents.TryGetValue(documentId.Uri, out document);
    }
  }
}
