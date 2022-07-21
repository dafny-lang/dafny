using System;
using System.Reactive.Linq;
using System.Reactive.Threading.Tasks;
using System.Threading;
using System.Threading.Tasks;

namespace Microsoft.Dafny.LanguageServer.Workspace;

class DocumentEntry : IDocumentEntry {
  private readonly CancellationTokenSource cancellationSource;
  public int? Version { get; }
  public DocumentTextBuffer TextBuffer { get; }
  public Task<DafnyDocument> ResolvedDocument { get; }
  public Task<DafnyDocument> TranslatedDocument { get; }
  public DafnyDocument LastPublishedDocument => Observer.LastPublishedDocument;

  private TaskCompletionSource verificationCompleted = new();
  public void RestartVerification() {
    if (verificationCompleted.Task.IsCompleted) {
      verificationCompleted = new TaskCompletionSource();
    }
  }

  public void EndVerification() {
    verificationCompleted.TrySetResult();
  }

  public Task<DafnyDocument> LastDocument => TranslatedDocument.ContinueWith(t => {
    if (t.IsCompletedSuccessfully) {
      return verificationCompleted.Task.ContinueWith(_ => t, TaskScheduler.Current).Unwrap();
    }

    return ResolvedDocument;
  }, TaskScheduler.Current).Unwrap();

  public DocumentEntry(int? version,
    DocumentTextBuffer textBuffer,
    Task<DafnyDocument> translatedDocument,
    CancellationTokenSource cancellationSource,
    DiagnosticsObserver observer) {
    this.cancellationSource = cancellationSource;
    Observer = observer;
    TranslatedDocument = translatedDocument;
    Version = version;
    TextBuffer = textBuffer;

    // Ensure ResolveDocument is only completed after LastPublishedDocument has been updated.
    ResolvedDocument = Observer.LastAndUpcomingPublishedDocuments.Where(d => d.Version == version && d.WasResolved).FirstAsync().ToTask();
  }

  public void CancelPendingUpdates() {
    EndVerification();
    cancellationSource.Cancel();
  }

  public DiagnosticsObserver Observer { get; }

  public void Observe(IObservable<DafnyDocument> updates) {
    updates.Subscribe(Observer);
  }

  public bool Idle => verificationCompleted.Task.IsCompleted;
}