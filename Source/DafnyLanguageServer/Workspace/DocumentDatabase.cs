using Microsoft.Dafny.LanguageServer.Workspace.ChangeProcessors;
using Microsoft.Extensions.Logging;
using Microsoft.Extensions.Options;
using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Reactive.Disposables;
using System.Reactive.Linq;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.Language;

namespace Microsoft.Dafny.LanguageServer.Workspace {

  /// <summary>
  /// Database that cancels pending document updates when new changes are incoming.
  /// </summary>
  /// <remarks>
  /// Only delta updates are supported and the API is not thread-safe.
  /// </remarks>
  public class DocumentDatabase : IDocumentDatabase {
    private readonly ILogger logger;
    private readonly ITelemetryPublisher telemetryPublisher;
    private readonly INotificationPublisher notificationPublisher;
    private readonly DocumentOptions options;
    private readonly Dictionary<DocumentUri, DocumentEntry> documents = new();
    private readonly ITextDocumentLoader documentLoader;
    private readonly ITextChangeProcessor textChangeProcessor;
    private readonly IRelocator relocator;

    private bool VerifyOnOpen => options.Verify == AutoVerification.OnChange;
    private bool VerifyOnChange => options.Verify == AutoVerification.OnChange;
    private bool VerifyOnSave => options.Verify == AutoVerification.OnSave;

    public DocumentDatabase(
      ILogger<DocumentDatabase> logger,
      ITelemetryPublisher telemetryPublisher,
      INotificationPublisher notificationPublisher,
      IOptions<DocumentOptions> options,
      ITextDocumentLoader documentLoader,
      ITextChangeProcessor textChangeProcessor,
      IRelocator relocator
    ) {
      this.logger = logger;
      this.telemetryPublisher = telemetryPublisher;
      this.notificationPublisher = notificationPublisher;
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
          await databaseEntry.LastDocument;
        } catch (TaskCanceledException) {
        }
        return true;
      }
      return false;
    }

    public void OpenDocument(DocumentTextBuffer document) {
      var cancellationSource = new CancellationTokenSource();
      var resolvedDocumentTask = OpenAsync(document, cancellationSource.Token);

      var observer = new DiagnosticsObserver(logger, telemetryPublisher, notificationPublisher, documentLoader, document);
      var translatedDocument = LoadVerificationTasksAsync(observer, resolvedDocumentTask, cancellationSource.Token);

      var documentEntry = new DocumentEntry(
        document.Version,
        document,
        translatedDocument,
        cancellationSource,
        observer
      );

      documents.Add(document.Uri, documentEntry);

      documentEntry.Observe(
        ToObservableSkipCancelledAndPublishExceptions(documentEntry, resolvedDocumentTask).Where(d => !d.LoadCanceled).
        Concat(ToObservableSkipCancelledAndPublishExceptions(documentEntry, translatedDocument)));

      if (VerifyOnOpen) {
        Verify(documentEntry, cancellationSource.Token);
      } else {
        documentEntry.MarkVerificationFinished();
      }

    }

    private async Task<DafnyDocument> OpenAsync(DocumentTextBuffer textDocument, CancellationToken cancellationToken) {
      try {
        var newDocument = await documentLoader.LoadAsync(textDocument, cancellationToken);
        notificationPublisher.PublishGutterIcons(newDocument, false);
        return newDocument;
      } catch (OperationCanceledException) {
        // We do not allow canceling the load of the placeholder document. Otherwise, other components
        // start to have to check for nullability in later stages such as change request processors.
        return documentLoader.CreateUnloaded(textDocument, CancellationToken.None);
      }
    }

    private void Verify(IDocumentEntry entry, CancellationToken cancellationToken) {
      var _ = entry.TranslatedDocument.ContinueWith(task => {

        if (task.IsCanceled || task.IsFaulted) {
          return;
        }

        var document = task.Result;

        if (!RequiresOnSaveVerification(document) || !document.CanDoVerification) {
          entry.MarkVerificationFinished();
          return;
        }

        var _ = documentLoader.VerifyAllTasksAsync(entry, document, cancellationToken);
      }, TaskScheduler.Current);
    }

    public void UpdateDocument(DidChangeTextDocumentParams documentChange) {
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
      var updatedText = textChangeProcessor.ApplyChange(databaseEntry.TextBuffer, documentChange, CancellationToken.None);
      var resolvedDocumentTask = GetResolvedDocumentAsync(updatedText, databaseEntry, documentChange, cancellationSource.Token);
      var translatedDocument = LoadVerificationTasksAsync(databaseEntry.Observer, resolvedDocumentTask, cancellationSource.Token);
      var entry = new DocumentEntry(
        documentChange.TextDocument.Version,
        updatedText,
        translatedDocument,
        cancellationSource,
        databaseEntry.Observer
      );
      documents[documentUri] = entry;
      entry.Observe(ToObservableSkipCancelledAndPublishExceptions(entry, resolvedDocumentTask)
        .Concat(ToObservableSkipCancelledAndPublishExceptions(entry, translatedDocument)));

      if (VerifyOnChange) {
        Verify(entry, cancellationSource.Token);
      } else {
        entry.MarkVerificationFinished();
      }
    }

    private async Task<DafnyDocument> GetResolvedDocumentAsync(DocumentTextBuffer updatedText, DocumentEntry documentEntry,
      DidChangeTextDocumentParams documentChange, CancellationToken cancellationToken) {

      var oldDocument = documentEntry.LastPublishedDocument;

      // We do not pass the cancellation token to the text change processor because the text has to be kept in sync with the LSP client.
      var oldVerificationDiagnostics = oldDocument.ImplementationIdToView;
      var migratedImplementationViews = MigrateImplementationViews(documentChange, oldVerificationDiagnostics);
      var migratedVerificationTree =
        relocator.RelocateVerificationTree(oldDocument.VerificationTree, updatedText.NumberOfLines, documentChange, CancellationToken.None);

      var migratedLastTouchedPositions =
        relocator.RelocatePositions(oldDocument.LastTouchedMethodPositions, documentChange, CancellationToken.None);
      try {
        var newDocument = await documentLoader.LoadAsync(updatedText, cancellationToken);
        var lastChange =
          documentChange.ContentChanges
            .Select(contentChange => contentChange.Range)
            .LastOrDefault(newDocument.LastChange);
        newDocument = newDocument with { LastChange = lastChange };
        if (newDocument.SymbolTable.Resolved) {
          var resolvedDocument = newDocument with {
            ImplementationIdToView = migratedImplementationViews,
            VerificationTree = migratedVerificationTree,
            LastTouchedMethodPositions = migratedLastTouchedPositions
          };
          notificationPublisher.PublishGutterIcons(resolvedDocument, false);
          return resolvedDocument;
        }
        // The document loader failed to create a new symbol table. Since we'd still like to provide
        // features such as code completion and lookup, we re-locate the previously resolved symbols
        // according to the change.
        var failedDocument = newDocument with {
          SymbolTable = relocator.RelocateSymbols(oldDocument.SymbolTable, documentChange, CancellationToken.None),
          ImplementationIdToView = migratedImplementationViews,
          VerificationTree = migratedVerificationTree,
          LastTouchedMethodPositions = migratedLastTouchedPositions
        };
        notificationPublisher.PublishGutterIcons(failedDocument, false);
        return failedDocument;
      } catch (OperationCanceledException) {
        // The document load was canceled before it could complete. We migrate the document
        // to re-locate symbols that were resolved previously.
        logger.LogTrace("document loading canceled, applying migration");
        return oldDocument with {
          TextDocumentItem = updatedText,
          SymbolTable = relocator.RelocateSymbols(oldDocument.SymbolTable, documentChange, CancellationToken.None),
          VerificationTree = migratedVerificationTree,
          LoadCanceled = true,
          ImplementationIdToView = migratedImplementationViews,
          LastTouchedMethodPositions = migratedLastTouchedPositions
        };
      }
    }

    private Dictionary<ImplementationId, ImplementationView> MigrateImplementationViews(DidChangeTextDocumentParams documentChange,
      IReadOnlyDictionary<ImplementationId, ImplementationView> oldVerificationDiagnostics) {
      var result = new Dictionary<ImplementationId, ImplementationView>();
      foreach (var entry in oldVerificationDiagnostics) {
        var newRange = relocator.RelocateRange(entry.Value.Range, documentChange, CancellationToken.None);
        if (newRange != null) {
          result.Add(entry.Key with {
            NamedVerificationTask = relocator.RelocatePosition(entry.Key.NamedVerificationTask, documentChange, CancellationToken.None)
          }, entry.Value with {
            Range = newRange,
            Diagnostics = relocator.RelocateDiagnostics(entry.Value.Diagnostics, documentChange, CancellationToken.None)
          });
        }
      }
      return result;
    }

    private async Task<DafnyDocument> LoadVerificationTasksAsync(DiagnosticsObserver observer, Task<DafnyDocument> resolvedDocumentTask, CancellationToken cancellationToken) {
#pragma warning disable VSTHRD003
      var resolvedDocument = await resolvedDocumentTask;
#pragma warning restore VSTHRD003
      await documentLoader.PrepareVerificationTasksAsync(resolvedDocument, cancellationToken);
      resolvedDocument.VerificationUpdates.Subscribe(observer);
      return resolvedDocument;
    }

    public void SaveDocument(TextDocumentIdentifier documentId) {
      if (!documents.TryGetValue(documentId.Uri, out var databaseEntry)) {
        throw new ArgumentException($"the document {documentId.Uri} was not loaded before");
      }
      if (!VerifyOnSave) {
        return;
      }

      var cancellationSource = new CancellationTokenSource();
      databaseEntry.MarkVerificationStarted();
      Verify(databaseEntry, cancellationSource.Token);
    }

    private static bool RequiresOnSaveVerification(DafnyDocument document) {
      return document.LoadCanceled || document.SymbolTable.Resolved;
    }

    public Task<DafnyDocument?> GetResolvedDocumentAsync(TextDocumentIdentifier documentId) {
      if (documents.TryGetValue(documentId.Uri, out var databaseEntry)) {
        return databaseEntry.ResolvedDocument!;
      }
      return Task.FromResult<DafnyDocument?>(null);
    }

    public Task<DafnyDocument?> GetLastDocumentAsync(TextDocumentIdentifier documentId) {
      if (documents.TryGetValue(documentId.Uri, out var databaseEntry)) {
        return databaseEntry.LastDocument!;
      }
      return Task.FromResult<DafnyDocument?>(null);
    }

    public IReadOnlyDictionary<DocumentUri, IDocumentEntry> Documents =>
      documents.ToDictionary(k => k.Key, v => (IDocumentEntry)v.Value);

    public IObservable<DafnyDocument> ToObservableSkipCancelledAndPublishExceptions(IDocumentEntry entry, Task<DafnyDocument> task) {
      return Observable.Create<DafnyDocument>(observer => {
        var _ = task.ContinueWith(t => {
          if (t.IsCompletedSuccessfully) {
            observer?.OnNext(t.Result);
          } else if (t.Exception != null) {
            var lastPublishedDocument = entry.LastPublishedDocument;
            var previousDiagnostics = lastPublishedDocument.LoadCanceled
              ? new Diagnostic[] { }
              : lastPublishedDocument.ParseAndResolutionDiagnostics;
            observer?.OnNext(lastPublishedDocument with {
              LoadCanceled = false,
              ParseAndResolutionDiagnostics = previousDiagnostics.Concat(new Diagnostic[] {
                new() {
                  Message = "Dafny encountered an internal error. Please report it at <https://github.com/dafny-lang/dafny/issues>.\n" + t.Exception,
                  Severity = DiagnosticSeverity.Error,
                  Range = lastPublishedDocument.Program.GetFirstTopLevelToken().GetLspRange(),
                  Source = "Crash"
                }
              }).ToList()
            });
            telemetryPublisher.PublishUnhandledException(t.Exception);
          }
          observer?.OnCompleted();
        }, TaskScheduler.Current);
        return Disposable.Create(() => observer = null);
      });
    }

  }
}
