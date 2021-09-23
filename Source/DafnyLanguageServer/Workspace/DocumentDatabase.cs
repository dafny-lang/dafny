using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Extensions.Options;
using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System;
using System.Collections.Generic;
using System.Diagnostics.CodeAnalysis;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;

namespace Microsoft.Dafny.LanguageServer.Workspace {
  /// <summary>
  /// Database that cancels pending document updates when new changes are incoming.
  /// </summary>
  /// <remarks>
  /// Only delta updates are supported and the API is not thread-safe.
  /// </remarks>
  public class DocumentDatabase : IDocumentDatabase {
    private readonly DocumentOptions _options;
    private readonly Dictionary<DocumentUri, DocumentEntry> _documents = new();
    private readonly ITextDocumentLoader _documentLoader;
    private readonly IDocumentUpdater _documentUpdater;

    private bool VerifyOnLoad => _options.Verify == AutoVerification.OnChange;
    private bool VerifyOnSave => _options.Verify == AutoVerification.OnSave;

    public DocumentDatabase(
      IOptions<DocumentOptions> options,
      ITextDocumentLoader documentLoader,
      IDocumentUpdater documentUpdater
    ) {
      _options = options.Value;
      _documentLoader = documentLoader;
      _documentUpdater = documentUpdater;
      CommandLineOptions.Clo.ProverOptions = GetProverOptions(_options);
    }

    private static List<string> GetProverOptions(DocumentOptions options) {
      return options.ProverOptions.Split(
        new[] { " ", "\n", "\t" },
        StringSplitOptions.RemoveEmptyEntries
      ).ToList();
    }

    public DafnyDocument? CloseDocument(TextDocumentIdentifier documentId) {
      if (_documents.Remove(documentId.Uri, out var databaseEntry)) {
        databaseEntry.CancelPendingUpdates();
        return databaseEntry.Document.Result;
      }
      return null;
    }

    public async Task<DafnyDocument> LoadDocumentAsync(TextDocumentItem document, CancellationToken cancellationToken) {
      var databaseEntry = new DocumentEntry(
        document.Version,
        // Do not allow cancelling the initial load.
        // TODO Allow cancelling when the document is closed.
        Task.Run(() => _documentLoader.LoadAsync(document, VerifyOnLoad, CancellationToken.None)),
        new CancellationTokenSource()
      );
      if (!_documents.TryAdd(document.Uri, databaseEntry)) {
        throw new InvalidOperationException($"the document {document.Uri} was already loaded");
      }
      return await databaseEntry.Document;
    }

    public async Task<DafnyDocument?> UpdateDocumentAsync(DidChangeTextDocumentParams documentChange, CancellationToken cancellationToken) {
      var documentUri = documentChange.TextDocument.Uri;
      if (!_documents.TryGetValue(documentUri, out var databaseEntry)) {
        throw new ArgumentException($"the document {documentUri} was not loaded before");
      }
      if (documentChange.TextDocument.Version < databaseEntry.Version) {
        throw new InvalidOperationException($"the updates of document {documentUri} are out-of-order");
      }
      databaseEntry.CancelPendingUpdates();
      var cancellationSource = new CancellationTokenSource();
      var updatedEntry = new DocumentEntry(
        documentChange.TextDocument.Version,
        // Do not allow cancelling the initial load.
        // TODO Allow cancelling when the document is closed.
        Task.Run(async () => await _documentUpdater.ApplyChangesAsync(await databaseEntry.Document, documentChange, cancellationSource.Token)),
        cancellationSource
      );
      _documents[documentUri] = updatedEntry;
      return await updatedEntry.Document;
    }

    public async Task<DafnyDocument?> SaveDocumentAsync(TextDocumentIdentifier documentId, CancellationToken cancellationToken) {
      if (!_documents.TryGetValue(documentId.Uri, out var databaseEntry)) {
        return null;
      }
      var document = await databaseEntry.Document;
      if (!VerifyOnSave) {
        return document;
      }
      var cancellationSource = new CancellationTokenSource();
      var updatedEntry = new DocumentEntry(
        document.Version,
        document.SymbolTable.Resolved
          ? Task.Run(() => _documentLoader.LoadAsync(document.Text, VerifyOnSave, cancellationSource.Token))
          : databaseEntry.Document,
        new CancellationTokenSource()
      );
      _documents[documentId.Uri] = updatedEntry;
      return await updatedEntry.Document;
    }

    public bool TryGetDocument(TextDocumentIdentifier documentId, [NotNullWhen(true)] out DafnyDocument? document) {
      // TODO make asynchronous? Requires refactoring of all unit tests.
      if (_documents.TryGetValue(documentId.Uri, out var databaseEntry)) {
        document = databaseEntry.Document.Result;
        return true;
      }
      document = null;
      return false;
    }

    private record DocumentEntry(int? Version, Task<DafnyDocument> Document, CancellationTokenSource CancellationSource) {
      public CancellationToken CancellationToken => CancellationSource.Token;

      public void CancelPendingUpdates() {
        CancellationSource.Cancel();
      }
    }
  }
}
