using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.ComponentModel.Composition;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Text.RegularExpressions;
using System.Threading;
using System.Windows;
using System.Windows.Media;
using System.Windows.Shapes;
using System.Windows.Threading;
using Microsoft.VisualStudio.Shell;
using Microsoft.VisualStudio.Text;
using Microsoft.VisualStudio.Text.Editor;
using Microsoft.VisualStudio.Text.Formatting;
using Microsoft.VisualStudio.Text.Tagging;
using Microsoft.VisualStudio.Utilities;
using Dafny = Microsoft.Dafny;


namespace DafnyLanguage
{

  #region UI stuff
  internal class ProgressMarginGlyphFactory : IGlyphFactory
  {
    public UIElement GenerateGlyph(IWpfTextViewLine line, IGlyphTag tag) {
      var dtag = tag as ProgressGlyphTag;
      if (dtag == null) {
        return null;
      }

      System.Windows.Shapes.Rectangle sh = new Rectangle() {
        Fill = dtag.Val == 0 ? Brushes.Violet : Brushes.DarkOrange,
        Height = 18.0,
        Width = 3.0
      };
      return sh;
    }
  }

  [Export(typeof(IGlyphFactoryProvider))]
  [Name("ProgressMarginGlyph")]
  [Order(After = "TokenTagger")]
  [ContentType("dafny")]
  [TagType(typeof(ProgressGlyphTag))]
  internal sealed class ProgressMarginGlyphFactoryProvider : IGlyphFactoryProvider
  {
    public IGlyphFactory GetGlyphFactory(IWpfTextView view, IWpfTextViewMargin margin) {
      return new ProgressMarginGlyphFactory();
    }
  }

  internal class ProgressGlyphTag : IGlyphTag
  {
    public readonly int Val;
    public ProgressGlyphTag(int val) {
      Val = val;
    }
  }
  #endregion


  #region Provider

  [Export(typeof(ITaggerProvider))]
  [ContentType("dafny")]
  [TagType(typeof(ProgressGlyphTag))]
  class ProgressTaggerProvider : ITaggerProvider
  {
    [Import]
    internal IBufferTagAggregatorFactoryService AggregatorFactory = null;

    [Import(typeof(Microsoft.VisualStudio.Shell.SVsServiceProvider))]
    internal IServiceProvider _serviceProvider = null;

    [Import]
    ITextDocumentFactoryService _textDocumentFactory = null;

    public ITagger<T> CreateTagger<T>(ITextBuffer buffer) where T : ITag {
      ITagAggregator<DafnyResolverTag> tagAggregator = AggregatorFactory.CreateTagAggregator<DafnyResolverTag>(buffer);
      // create a single tagger for each buffer.
      Func<ITagger<T>> sc = delegate() { return new ProgressTagger(buffer, _serviceProvider, tagAggregator, _textDocumentFactory) as ITagger<T>; };
      return buffer.Properties.GetOrCreateSingletonProperty<ITagger<T>>(sc);
    }
  }

  #endregion


  #region Tagger

  public class ProgressTagger : ITagger<ProgressGlyphTag>, IDisposable
  {
    ErrorListProvider _errorProvider;
    ITextBuffer _buffer;
    ITextDocument _document;

    readonly DispatcherTimer timer;

    public ProgressTagger(ITextBuffer buffer, IServiceProvider serviceProvider, ITagAggregator<DafnyResolverTag> tagAggregator, ITextDocumentFactoryService textDocumentFactory) {
      _buffer = buffer;

      if (!textDocumentFactory.TryGetTextDocument(_buffer, out _document))
      {
        _document = null;
      }

      _errorProvider = new ErrorListProvider(serviceProvider);

      timer = new DispatcherTimer(DispatcherPriority.ApplicationIdle);
      timer.Interval = TimeSpan.FromMilliseconds(500);
      timer.Tick += new EventHandler(UponIdle);

      tagAggregator.TagsChanged += new EventHandler<TagsChangedEventArgs>(_aggregator_TagsChanged);
      buffer.Changed += new EventHandler<TextContentChangedEventArgs>(buffer_Changed);
      bufferChangesPostVerificationStart.Add(new SnapshotSpan(buffer.CurrentSnapshot, 0, buffer.CurrentSnapshot.Length));
    }

    public void Dispose()
    {
      Dispose(true);
      GC.SuppressFinalize(this);
    }

    private void Dispose(bool disposing)
    {
      if (!m_disposed)
      {
        if (disposing)
        {
          _buffer.Changed -= buffer_Changed;
          _errorProvider.Dispose();
          if (resolver != null)
          {
            resolver.Dispose();
          }
        }

        m_disposed = true;
      }
    }

    // The following fields and the contents of the following two lists are protected by the lock "this".
    List<SnapshotSpan> bufferChangesPreVerificationStart = new List<SnapshotSpan>();  // buffer changes after the last completed verification and before the currently running verification
    List<SnapshotSpan> bufferChangesPostVerificationStart = new List<SnapshotSpan>();  // buffer changes since the start of the currently running verification

    void buffer_Changed(object sender, TextContentChangedEventArgs e) {
      lock (this) {
        foreach (var change in e.Changes) {
          var startLine = e.After.GetLineFromPosition(change.NewPosition);
          var endLine = e.After.GetLineFromPosition(change.NewEnd);
          bufferChangesPostVerificationStart.Add(new SnapshotSpan(startLine.Start, endLine.End));
        }
      }
    }

    // The next field is protected by "this"
    ResolverTagger resolver;
    // Keep track of the most recent resolution results.
    void _aggregator_TagsChanged(object sender, TagsChangedEventArgs e) {
      var r = sender as ResolverTagger;
      if (r != null) {
        lock (this) {
          resolver = r;
        }
        timer.Stop();
        timer.Start();
      }
    }

    bool verificationInProgress;  // this field is protected by "this".  Invariant:  !verificationInProgress ==> bufferChangesPreVerificationStart.Count == 0
    Thread verificationWorker;
    bool verificationDisabled;

    public bool VerificationDisabled
    {
      get { return verificationDisabled; }
    }

    public static readonly IDictionary<string, ProgressTagger> ProgressTaggers = new ConcurrentDictionary<string, ProgressTagger>();

    public readonly ConcurrentDictionary<string, ITextSnapshot> RequestIdToSnapshot = new ConcurrentDictionary<string, ITextSnapshot>();

    /// <summary>
    /// This method is invoked when the user has been idle for a little while.
    /// Note, "sender" and "args" are allowed to be passed in as null--they are not used by this method.
    /// </summary>
    public void UponIdle(object sender, EventArgs args) {
      Dafny.Program prog;
      ITextSnapshot snap;
      lock (this) {
        if (verificationInProgress) {
          // This UponIdle message came at an inopportune time--we've already kicked off a verification.
          // Just back off.
          return;
        }

        if (resolver == null) return;
        lock (resolver) {
          prog = resolver._program;
          snap = resolver._snapshot;
        }
        if (prog == null || verificationDisabled) return;
        // We have a successfully resolved program to verify

        var resolvedVersion = snap.Version.VersionNumber;
        if (bufferChangesPostVerificationStart.Count == 0) {
          // Nothing new to verify.  No reason to start a new verification.
          return;
        } else if (!bufferChangesPostVerificationStart.TrueForAll(span => span.Snapshot.Version.VersionNumber <= resolvedVersion)) {
          // There have been buffer changes since the program that was resolved.  Do nothing here,
          // and instead just await the next resolved program.
          return;
        }

        // at this time, we're committed to running the verifier
        verificationInProgress = true;

        // Change orange progress markers into yellow ones
        Contract.Assert(bufferChangesPreVerificationStart.Count == 0);  // follows from monitor invariant
        var empty = bufferChangesPreVerificationStart;
        bufferChangesPreVerificationStart = bufferChangesPostVerificationStart;
        bufferChangesPostVerificationStart = empty;

        // Notify to-whom-it-may-concern about the changes we just made
        NotifyAboutChangedTags(snap);

        string requestId = null;
        lock (RequestIdToSnapshot)
        {
          do
          {
            requestId = DateTime.UtcNow.Ticks.ToString();
          } while (RequestIdToSnapshot.ContainsKey(requestId));
          RequestIdToSnapshot[requestId] = snap;
        }

        verificationWorker = new Thread(() => VerificationWorker(prog, snap, requestId, resolver));
        verificationWorker.IsBackground = true;
        if (_document != null)
        {
          ProgressTaggers[_document.FilePath] = this;
        }
      }
      verificationWorker.Start();
    }

    private void NotifyAboutChangedTags(ITextSnapshot snap)
    {
      var chng = TagsChanged;
      if (chng != null)
      {
        chng(this, new SnapshotSpanEventArgs(new SnapshotSpan(snap, 0, snap.Length)));
      }
    }

    public void StopVerification()
    {
      verificationWorker.Abort();  // TODO(wuestholz): Make sure this kills the corresponding Z3 process.
      lock (this)
      {
        bufferChangesPreVerificationStart.Clear();
        bufferChangesPostVerificationStart.Clear();
        bufferChangesPostVerificationStart.Add(new SnapshotSpan(_buffer.CurrentSnapshot, 0, _buffer.CurrentSnapshot.Length));
        verificationDisabled = true;
        verificationInProgress = false;
        NotifyAboutChangedTags(_buffer.CurrentSnapshot);
      }
    }

    public void StartVerification()
    {
      lock (this)
      {
        bufferChangesPreVerificationStart.Clear();
        bufferChangesPostVerificationStart.Clear();
        bufferChangesPostVerificationStart.Add(new SnapshotSpan(_buffer.CurrentSnapshot, 0, _buffer.CurrentSnapshot.Length));
        verificationDisabled = false;
        if (_document != null)
        {
          Microsoft.Boogie.ExecutionEngine.Cache.RemoveMatchingKeys(new Regex(string.Format(@"^{0}", Regex.Escape(GetHashCode().ToString()))));
        }
        NotifyAboutChangedTags(_buffer.CurrentSnapshot);
      }
    }


    /// <summary>
    /// Thread entry point.
    /// </summary>
    void VerificationWorker(Dafny.Program program, ITextSnapshot snapshot, string requestId, ResolverTagger errorListHolder) {
      Contract.Requires(program != null);
      Contract.Requires(snapshot != null);
      Contract.Requires(requestId != null);
      Contract.Requires(errorListHolder != null);

      // Run the verifier
      var newErrors = new List<DafnyError>();
      try
      {
        bool success = DafnyDriver.Verify(program, GetHashCode().ToString(), requestId, errorInfo =>
        {
          if (errorInfo.RequestId != null && RequestIdToSnapshot.ContainsKey(errorInfo.RequestId))
          {
            var s = RequestIdToSnapshot[errorInfo.RequestId];
            newErrors.Add(new DafnyError(errorInfo.Tok.line - 1, errorInfo.Tok.col - 1, ErrorCategory.VerificationError, errorInfo.FullMsg, s));
            foreach (var aux in errorInfo.Aux)
            {
              newErrors.Add(new DafnyError(aux.Tok.line - 1, aux.Tok.col - 1, ErrorCategory.AuxInformation, aux.FullMsg, s));
            }
          }
        });
        if (!success)
        {
          newErrors.Add(new DafnyError(0, 0, ErrorCategory.InternalError, "Verification process error", snapshot));
        }
      }
      catch (Exception e)
      {
        newErrors.Add(new DafnyError(0, 0, ErrorCategory.InternalError, "Verification process error: " + e.Message, snapshot));
      }

      errorListHolder.VerificationErrors = newErrors;
      errorListHolder.UpdateErrorList(snapshot);

      lock (this) {
        bufferChangesPreVerificationStart.Clear();
        verificationInProgress = false;
      }
      // Notify to-whom-it-may-concern about the cleared pre-verification changes
      NotifyAboutChangedTags(snapshot);

      // If new changes took place since we started the verification, we may need to kick off another verification
      // immediately.
      UponIdle(null, null);
    }

    public event EventHandler<SnapshotSpanEventArgs> TagsChanged;
    private bool m_disposed;
    IEnumerable<ITagSpan<ProgressGlyphTag>> ITagger<ProgressGlyphTag>.GetTags(NormalizedSnapshotSpanCollection spans) {
      if (spans.Count == 0) yield break;
      var targetSnapshot = spans[0].Snapshot;

      List<SnapshotSpan> pre;
      List<SnapshotSpan> post;
      lock (this) {
        pre = bufferChangesPreVerificationStart;
        post = bufferChangesPostVerificationStart;
      }

      // If the requested snapshot isn't the same as the one our words are on, translate our spans to the expected snapshot
      var chs = new NormalizedSnapshotSpanCollection(pre.Select(span => span.TranslateTo(targetSnapshot, SpanTrackingMode.EdgeExclusive)));
      foreach (SnapshotSpan span in NormalizedSnapshotSpanCollection.Overlap(spans, chs)) {
        yield return new TagSpan<ProgressGlyphTag>(span, new ProgressGlyphTag(0));
      }
      chs = new NormalizedSnapshotSpanCollection(post.Select(span => span.TranslateTo(targetSnapshot, SpanTrackingMode.EdgeExclusive)));
      foreach (SnapshotSpan span in NormalizedSnapshotSpanCollection.Overlap(spans, chs)) {
        yield return new TagSpan<ProgressGlyphTag>(span, new ProgressGlyphTag(1));
      }
    }
  }

  #endregion

}
