using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.Language;
using Microsoft.Dafny.LanguageServer.Workspace.ChangeProcessors;
using Microsoft.Extensions.Logging;
using Microsoft.Extensions.Options;
using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System;
using System.Collections.Generic;
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
    private readonly ILogger logger;
    private readonly DocumentOptions options;
    private readonly Dictionary<DocumentUri, DocumentEntry> documents = new();
    private readonly ITextDocumentLoader documentLoader;
    private readonly ITextChangeProcessor textChangeProcessor;
    private readonly ISymbolTableRelocator symbolTableRelocator;

    private bool VerifyOnLoad => options.Verify == AutoVerification.OnChange;
    private bool VerifyOnChange => options.Verify == AutoVerification.OnChange;
    private bool VerifyOnSave => options.Verify == AutoVerification.OnSave;

    public DocumentDatabase(
      ILogger<DocumentDatabase> logger,
      IOptions<DocumentOptions> options,
      ITextDocumentLoader documentLoader,
      ITextChangeProcessor textChangeProcessor,
      ISymbolTableRelocator symbolTableRelocator
    ) {
      this.logger = logger;
      this.options = options.Value;
      this.documentLoader = documentLoader;
      this.textChangeProcessor = textChangeProcessor;
      this.symbolTableRelocator = symbolTableRelocator;
      CommandLineOptions.Clo.ProverOptions = GetProverOptions(this.options);
    }

    private static List<string> GetProverOptions(DocumentOptions options) {
      return options.ProverOptions.Split(
        new[] { " ", "\n", "\t" },
        StringSplitOptions.RemoveEmptyEntries
      ).ToList();
    }

    public async Task<bool> CloseDocumentAsync(TextDocumentIdentifier documentId) {
      if (documents.Remove(documentId.Uri, out var databaseEntry)) {
        databaseEntry.CancelPendingUpdates();
        await databaseEntry.Document;
        return true;
      }
      return false;
    }

    public async Task<DafnyDocument> LoadDocumentAsync(TextDocumentItem document) {
      var cancellationSource = new CancellationTokenSource();
      var databaseEntry = new DocumentEntry(
        document.Version,
        Task.Run(() => LoadAsync(document, cancellationSource.Token)),
        cancellationSource
      );
      documents.Add(document.Uri, databaseEntry);
      return await databaseEntry.Document;
    }

    private async Task<DafnyDocument> LoadAsync(TextDocumentItem document, CancellationToken cancellationToken) {
      try {
        return await documentLoader.LoadAsync(document, VerifyOnLoad, cancellationToken);
      } catch (OperationCanceledException) {
        // We do not allow cancelling the load of the placeholder document. Otherwise, other components
        // start to have to check for nullability in later stages such as change request processors.
        return documentLoader.CreateUnloaded(document, CancellationToken.None);
      }
    }

    public async Task<DafnyDocument> UpdateDocumentAsync(DidChangeTextDocumentParams documentChange) {
      var documentUri = documentChange.TextDocument.Uri;
      if (!documents.TryGetValue(documentUri, out var databaseEntry)) {
        throw new ArgumentException($"the document {documentUri} was not loaded before");
      }
      if (documentChange.TextDocument.Version != databaseEntry.Version + 1) {
        throw new InvalidOperationException($"the updates of document {documentUri} are out-of-order");
      }
      databaseEntry.CancelPendingUpdates();
      var cancellationSource = new CancellationTokenSource();
      var updatedEntry = new DocumentEntry(
        documentChange.TextDocument.Version,
        Task.Run(async () => await ApplyChangesAsync(await databaseEntry.Document, documentChange, cancellationSource.Token)),
        cancellationSource
      );
      documents[documentUri] = updatedEntry;
      return await updatedEntry.Document;
    }

    private async Task<DafnyDocument> ApplyChangesAsync(DafnyDocument oldDocument, DidChangeTextDocumentParams documentChange, CancellationToken cancellationToken) {
      // We do not pass the cancellation token to the text change processor because the text has to be kept in sync with the LSP client.
      var updatedText = textChangeProcessor.ApplyChange(oldDocument.Text, documentChange, CancellationToken.None);
      try {
        var newDocument = await documentLoader.LoadAsync(updatedText, VerifyOnChange, cancellationToken);
        if (newDocument.SymbolTable.Resolved) {
          return newDocument;
        }
        // The document loader failed to create a new symbol table. Since we'd still like to provide
        // features such as code completion and lookup, we re-locate the previously resolved symbols
        // according to the change.
        return newDocument with {
          SymbolTable = symbolTableRelocator.Relocate(oldDocument.SymbolTable, documentChange, CancellationToken.None)
        };
      } catch (OperationCanceledException) {
        // The document load was canceled before it could complete. We migrate the document
        // to re-locate symbols that were resolved previously.
        logger.LogTrace("document loading canceled, applying migration");
        return oldDocument with {
          Text = updatedText,
          SymbolTable = symbolTableRelocator.Relocate(oldDocument.SymbolTable, documentChange, CancellationToken.None),
          SerializedCounterExamples = null,
          LoadCanceled = true
        };
      }
    }

    public Task<DafnyDocument> SaveDocumentAsync(TextDocumentIdentifier documentId) {
      if (!documents.TryGetValue(documentId.Uri, out var databaseEntry)) {
        return Task.FromException<DafnyDocument>(new ArgumentException($"the document {documentId.Uri} was not loaded before"));
      }
      if (!VerifyOnSave) {
        return databaseEntry.Document;
      }
      return VerifyDocumentIfRequiredAsync(databaseEntry);
    }

    private async Task<DafnyDocument> VerifyDocumentIfRequiredAsync(DocumentEntry databaseEntry) {
      // The verification of a document is currently tied to a document load (see DocumentLoader.LoadAsync).
      // Therefore, we cancel any pending document load process and re-load it here with the verification.
      // In the future, the verification should be separated from the document load to have better
      // control over it.
      databaseEntry.CancelPendingUpdates();
      var document = await databaseEntry.Document;
      if (!RequiresOnSaveVerification(document)) {
        return document;
      }
      var updatedEntry = VerifyDocument(document);
      documents[document.Uri] = updatedEntry;
      return await updatedEntry.Document;
    }

    private DocumentEntry VerifyDocument(DafnyDocument document) {
      var cancellationSource = new CancellationTokenSource();
      var updatedEntry = new DocumentEntry(
        document.Version,
        Task.Run(() => documentLoader.LoadAsync(document.Text, VerifyOnSave, cancellationSource.Token)),
        cancellationSource
      );
      return updatedEntry;
    }

    private static bool RequiresOnSaveVerification(DafnyDocument document) {
      return document.LoadCanceled || document.SymbolTable.Resolved;
    }

    public async Task<DafnyDocument?> GetDocumentAsync(TextDocumentIdentifier documentId) {
      if (documents.TryGetValue(documentId.Uri, out var databaseEntry)) {
        return await databaseEntry.Document;
      }
      return null;
    }

    private record DocumentEntry(int? Version, Task<DafnyDocument> Document, CancellationTokenSource CancellationSource) {
      public void CancelPendingUpdates() {
        CancellationSource.Cancel();
      }
    }
  }
}
