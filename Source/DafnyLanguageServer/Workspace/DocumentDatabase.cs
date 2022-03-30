using Microsoft.Boogie;
using Microsoft.Dafny.LanguageServer.Workspace.ChangeProcessors;
using Microsoft.Extensions.Logging;
using Microsoft.Extensions.Options;
using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Reactive.Linq;
using System.Reactive.Threading.Tasks;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.Util;

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
    private readonly Dictionary<DocumentUri, DocumentDatabase.DocumentEntry> documents = new();
    private readonly ITextDocumentLoader documentLoader;
    private readonly ITextChangeProcessor textChangeProcessor;
    private readonly IRelocator relocator;

    private bool VerifyOnOpen => options.Verify == AutoVerification.OnChange;
    private bool VerifyOnChange => options.Verify == AutoVerification.OnChange;
    private bool VerifyOnSave => options.Verify == AutoVerification.OnSave;

    public DocumentDatabase(
      ILogger<DocumentDatabase> logger,
      IOptions<DocumentOptions> options,
      ITextDocumentLoader documentLoader,
      ITextChangeProcessor textChangeProcessor,
      IRelocator relocator
    ) {
      this.logger = logger;
      this.options = options.Value;
      this.documentLoader = documentLoader;
      this.textChangeProcessor = textChangeProcessor;
      this.relocator = relocator;
      DafnyOptions.O.ProverOptions = GetProverOptions(this.options);
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
        try {
          await databaseEntry.VerifiedDocument;
        } catch (TaskCanceledException) {
        }
        return true;
      }
      return false;
    }

    public IObservable<DafnyDocument> OpenDocument(TextDocumentItem document) {
      var cancellationSource = new CancellationTokenSource();
      var resolvedDocument = OpenAsync(document, cancellationSource.Token);
      var verifiedDocument = VerifyAsync(resolvedDocument, VerifyOnOpen, cancellationSource.Token);
      var databaseEntry = new DocumentEntry(
        document.Version,
        resolvedDocument,
        verifiedDocument,
        cancellationSource
      );
      documents.Add(document.Uri, databaseEntry);
      return resolvedDocument.ToObservable().Where(d => !d.LoadCanceled).Concat(verifiedDocument.ToObservable());
    }

    private async Task<DafnyDocument> OpenAsync(TextDocumentItem textDocument, CancellationToken cancellationToken) {
      try {
        return await documentLoader.LoadAsync(textDocument, cancellationToken);
      } catch (OperationCanceledException) {
        // We do not allow canceling the load of the placeholder document. Otherwise, other components
        // start to have to check for nullability in later stages such as change request processors.
        return documentLoader.CreateUnloaded(textDocument, CancellationToken.None);
      }
    }

    private async Task<DafnyDocument> VerifyAsync(Task<DafnyDocument> documentTask, bool verify, CancellationToken cancellationToken) {
#pragma warning disable VSTHRD003
      var document = await documentTask;
#pragma warning restore VSTHRD003
      if (document.LoadCanceled || !verify || document.Errors.HasErrors) {
        throw new TaskCanceledException();
      }
      return await documentLoader.VerifyAsync(document, cancellationToken);
    }

    public IObservable<DafnyDocument> UpdateDocument(DidChangeTextDocumentParams documentChange) {
      var documentUri = documentChange.TextDocument.Uri;
      if (!documents.TryGetValue(documentUri, out var databaseEntry)) {
        throw new ArgumentException($"the document {documentUri} was not loaded before");
      }

      // According to the LSP specification, document versions should increase monotonically but may be non-consecutive.
      // See: https://github.com/microsoft/language-server-protocol/blob/gh-pages/_specifications/specification-3-16.md?plain=1#L1195
      var oldVer = databaseEntry.Version;
      var newVer = documentChange.TextDocument.Version;
      if (oldVer >= newVer) {
        throw new InvalidOperationException(
          $"the updates of document {documentUri} are out-of-order: {oldVer} -> {newVer}");
      }

      databaseEntry.CancelPendingUpdates();
      var cancellationSource = new CancellationTokenSource();
      var previousDocumentTask = databaseEntry.VerifiedDocument.IsCompletedSuccessfully ? databaseEntry.VerifiedDocument : databaseEntry.ResolvedDocument;
      var resolvedDocumentTask = ApplyChangesAsync(previousDocumentTask, documentChange, cancellationSource.Token);
      var verifiedDocument = VerifyAsync(resolvedDocumentTask, VerifyOnChange, cancellationSource.Token);
      var updatedEntry = new DocumentEntry(
        documentChange.TextDocument.Version,
        resolvedDocumentTask,
        verifiedDocument,
        cancellationSource
      );
      documents[documentUri] = updatedEntry;
      return resolvedDocumentTask.ToObservable().Concat(verifiedDocument.ToObservable());
    }


    private async Task<DafnyDocument> ApplyChangesAsync(Task<DafnyDocument> oldDocumentTask, DidChangeTextDocumentParams documentChange, CancellationToken cancellationToken) {
#pragma warning disable VSTHRD003
      var oldDocument = await oldDocumentTask;
#pragma warning restore VSTHRD003
      // We do not pass the cancellation token to the text change processor because the text has to be kept in sync with the LSP client.
      var updatedText = textChangeProcessor.ApplyChange(oldDocument.Text, documentChange, CancellationToken.None);
      var oldVerificationDiagnostics =
        oldDocument.Errors.GetDiagnostics(oldDocument.Uri).Where(d => d.Source == MessageSource.Verifier.ToString()).
          Concat(oldDocument.OldVerificationDiagnostics).ToList();
      var migratedVerificationDiagnotics =
        relocator.RelocateDiagnostics(oldVerificationDiagnostics, documentChange, CancellationToken.None);
      logger.LogDebug($"Migrated {oldVerificationDiagnostics.Count} diagnostics into {migratedVerificationDiagnotics.Count} diagnostics.");
      try {
        var newDocument = await documentLoader.LoadAsync(updatedText, cancellationToken);
        if (newDocument.SymbolTable.Resolved) {
          return newDocument with {
            OldVerificationDiagnostics = migratedVerificationDiagnotics
          };
        }
        // The document loader failed to create a new symbol table. Since we'd still like to provide
        // features such as code completion and lookup, we re-locate the previously resolved symbols
        // according to the change.
        return newDocument with {
          SymbolTable = relocator.RelocateSymbols(oldDocument.SymbolTable, documentChange, CancellationToken.None),
          OldVerificationDiagnostics = migratedVerificationDiagnotics
        };
      } catch (OperationCanceledException) {
        // The document load was canceled before it could complete. We migrate the document
        // to re-locate symbols that were resolved previously.
        logger.LogTrace("document loading canceled, applying migration");
        return oldDocument with {
          Text = updatedText,
          SymbolTable = relocator.RelocateSymbols(oldDocument.SymbolTable, documentChange, CancellationToken.None),
          SerializedCounterExamples = null,
          LoadCanceled = true,
          OldVerificationDiagnostics = migratedVerificationDiagnotics
        };
      }
    }

    public IObservable<DafnyDocument> SaveDocument(TextDocumentIdentifier documentId) {
      if (!documents.TryGetValue(documentId.Uri, out var databaseEntry)) {
        throw new ArgumentException($"the document {documentId.Uri} was not loaded before");
      }
      if (!VerifyOnSave) {
        return Observable.Empty<DafnyDocument>();
      }

      var cancellationSource = new CancellationTokenSource();
      var verifiedDocumentTask = VerifyDocumentIfRequiredAsync(databaseEntry, cancellationSource.Token);
      var updatedEntry = new DocumentEntry(
        databaseEntry.Version,
        databaseEntry.ResolvedDocument,
        verifiedDocumentTask,
        cancellationSource
      );
      documents[documentId.Uri] = updatedEntry;
      return verifiedDocumentTask.ToObservable();
    }

    private async Task<DafnyDocument> VerifyDocumentIfRequiredAsync(IDocumentEntry databaseEntry, CancellationToken cancellationToken) {
      var document = await databaseEntry.ResolvedDocument;
      if (!RequiresOnSaveVerification(document)) {
        throw new TaskCanceledException();
      }
      var verifiedDocumentTask = documentLoader.VerifyAsync(document, cancellationToken);
      return await verifiedDocumentTask;
    }

    private static bool RequiresOnSaveVerification(DafnyDocument document) {
      return document.LoadCanceled || document.SymbolTable.Resolved;
    }

    public async Task<DafnyDocument?> GetDocumentAsync(TextDocumentIdentifier documentId) {
      if (documents.TryGetValue(documentId.Uri, out var databaseEntry)) {
        return await databaseEntry.ResolvedDocument;
      }
      return null;
    }

    public async Task<DafnyDocument?> GetVerifiedDocumentAsync(TextDocumentIdentifier documentId) {
      if (documents.TryGetValue(documentId.Uri, out var databaseEntry)) {
        return await databaseEntry.VerifiedDocument;
      }
      return null;
    }

    public IReadOnlyDictionary<DocumentUri, IDocumentEntry> Documents =>
      documents.ToDictionary(k => k.Key, v => (IDocumentEntry)v.Value);

    private record DocumentEntry(int? Version, Task<DafnyDocument> ResolvedDocument,
      Task<DafnyDocument> VerifiedDocument,
      CancellationTokenSource CancellationSource) : IDocumentEntry {
      public void CancelPendingUpdates() {
        CancellationSource.Cancel();
      }
    }
  }
}
