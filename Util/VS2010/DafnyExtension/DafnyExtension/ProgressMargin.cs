using System;
using System.Collections.Generic;
using System.Threading;
using System.Windows;
using System.Windows.Shapes;
using System.Windows.Media;
using System.Windows.Controls;
using System.ComponentModel.Composition;
using Microsoft.VisualStudio.Text;
using Microsoft.VisualStudio.Text.Editor;
using Microsoft.VisualStudio.Text.Formatting;
using Microsoft.VisualStudio.Text.Tagging;
using Microsoft.VisualStudio.Text.Classification;
using Microsoft.VisualStudio.Shell;
using Microsoft.VisualStudio.Utilities;
using System.Diagnostics.Contracts;
using Dafny = Microsoft.Dafny;
using Bpl = Microsoft.Boogie;


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
        Fill = dtag.Val == 0 ? new SolidColorBrush(Color.FromRgb(255, 238, 98)) : Brushes.DarkOrange,
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

  [Export(typeof(ITaggerProvider))]
  [ContentType("dafny")]
  [TagType(typeof(ProgressGlyphTag))]
  class ProgressTaggerProvider : ITaggerProvider
  {
    [Import]
    internal IBufferTagAggregatorFactoryService AggregatorFactory = null;

    [Import(typeof(Microsoft.VisualStudio.Shell.SVsServiceProvider))]
    internal IServiceProvider _serviceProvider = null;

    public ITagger<T> CreateTagger<T>(ITextBuffer buffer) where T : ITag {
      ITagAggregator<DafnyResolverTag> tagAggregator = AggregatorFactory.CreateTagAggregator<DafnyResolverTag>(buffer);
      // create a single tagger for each buffer.
      Func<ITagger<T>> sc = delegate() { return new ProgressTagger(buffer, _serviceProvider, tagAggregator) as ITagger<T>; };
      return buffer.Properties.GetOrCreateSingletonProperty<ITagger<T>>(sc);
    }
  }

  internal class ProgressTagger : ITagger<ProgressGlyphTag>
  {
    ErrorListProvider _errorProvider;
    ITextBuffer _buffer;

    public ProgressTagger(ITextBuffer buffer, IServiceProvider serviceProvider, ITagAggregator<DafnyResolverTag> tagAggregator) {
      _buffer = buffer;
      _errorProvider = new ErrorListProvider(serviceProvider);
      BufferIdleEventUtil.AddBufferIdleEventListener(buffer, DoTheVerification);
      tagAggregator.TagsChanged += new EventHandler<TagsChangedEventArgs>(_aggregator_TagsChanged);
      buffer.Changed += new EventHandler<TextContentChangedEventArgs>(buffer_Changed);
      bufferChangesPostVerificationStart.Add(new SnapshotSpan(buffer.CurrentSnapshot, 0, buffer.CurrentSnapshot.Length));
    }

    public void Dispose() {
      BufferIdleEventUtil.RemoveBufferIdleEventListener(_buffer, DoTheVerification);
    }

    // The next two fields are protected by the lock "this".  The lists pointed to by the
    // fields are not to be modified.
    List<SnapshotSpan> bufferChangesPreVerificationStart = new List<SnapshotSpan>();  // buffer changes after the last completed verification and before the currently running verification
    List<SnapshotSpan> bufferChangesPostVerificationStart = new List<SnapshotSpan>();  // buffer changes since the start of the currently running verification
    void buffer_Changed(object sender, TextContentChangedEventArgs e) {
      var chng = TagsChanged;
      if (chng != null) {
        foreach (var change in e.Changes) {
          var startLine = e.After.GetLineFromPosition(change.NewPosition);
          var endLine = e.After.GetLineFromPosition(change.NewEnd);
          bufferChangesPostVerificationStart.Add(new SnapshotSpan(startLine.Start, endLine.End));
        }
      }
    }

    // Keep track of the most recent resolution results
    ResolverTagger resolver;
    Dafny.Program latestProgram;
    ITextSnapshot latestSnapshot;
    void _aggregator_TagsChanged(object sender, TagsChangedEventArgs e) {
      var r = sender as ResolverTagger;
      if (r != null) {
        // If r._program is null, then the current buffer contains a Dafny fragment that does not resolve.  If it is non-null,
        // then r._program has been successfully resolved, so when things have been sufficiently idle, we're ready to verify it.
        resolver = r;
        lock (r) {
          latestProgram = r._program;
          latestSnapshot = latestProgram != null ? r._snapshot : null;
        }
      }
    }

    bool verificationInProgress;  // this field is protected by "this"
    bool verificationRequested;  // this field is protected by "this".  Invariant:  verificationRequested ==> verificationInProgress
    public void DoTheVerification(object sender, EventArgs args) {
      var buffer = sender as ITextBuffer;
      if (buffer != null && latestProgram != null && resolver != null) {
        bool tagsChanged = false;
        lock (this) {
          if (verificationInProgress) {
            verificationRequested = true;
            return;
          }
          verificationInProgress = true;
          // In the following, accomplish:  pre, post := pre+post, {};
          if (bufferChangesPostVerificationStart.Count != 0) {
            tagsChanged = true;
            if (bufferChangesPreVerificationStart.Count == 0) {
              var empty = bufferChangesPreVerificationStart;
              bufferChangesPreVerificationStart = bufferChangesPostVerificationStart;
              bufferChangesPostVerificationStart = empty;
            } else {
              var all = new List<SnapshotSpan>();
              all.AddRange(bufferChangesPreVerificationStart);
              all.AddRange(bufferChangesPostVerificationStart);
              bufferChangesPreVerificationStart = all;
              bufferChangesPostVerificationStart = new List<SnapshotSpan>();
            }
          }
        }

        // kick off the verification
        var w = new VerificationWorker(latestProgram, resolver, this, latestSnapshot);
        var thread = new Thread(w.Start);
        thread.Start();

        var chng = TagsChanged;
        if (tagsChanged && chng != null) {
          var snap = latestSnapshot;
          chng(this, new SnapshotSpanEventArgs(new SnapshotSpan(snap, 0, snap.Length)));
        }
      }
    }

    class VerificationWorker
    {
      readonly Dafny.Program program;
      readonly ResolverTagger resolver;
      readonly ProgressTagger pt;
      readonly ITextSnapshot snapshot;
      public VerificationWorker(Dafny.Program program, ResolverTagger resolver, ProgressTagger pt, ITextSnapshot snapshot) {
        Contract.Requires(program != null);
        Contract.Requires(resolver != null);
        Contract.Requires(pt != null);
        Contract.Requires(snapshot != null);
        this.program = program;
        this.resolver = resolver;
        this.pt = pt;
        this.snapshot = snapshot;
      }

      public void Start() {
        bool verifySomeMore = true;
        while (verifySomeMore) {
          var newErrors = new List<DafnyError>();
          bool success = DafnyDriver.Verify(program, errorInfo => {
            newErrors.Add(new DafnyError(errorInfo.Tok.line - 1, errorInfo.Tok.col - 1, ErrorCategory.VerificationError, errorInfo.Msg));
            foreach (var aux in errorInfo.Aux) {
              newErrors.Add(new DafnyError(aux.Tok.line - 1, aux.Tok.col - 1, ErrorCategory.AuxInformation, aux.Msg));
            }
          });

          lock (pt) {
            verifySomeMore = pt.verificationRequested;
            pt.verificationInProgress = verifySomeMore;
            pt.verificationRequested = false;
            if (pt.bufferChangesPreVerificationStart.Count != 0) {
              pt.bufferChangesPreVerificationStart = new List<SnapshotSpan>();
            }
            resolver.PopulateErrorList(newErrors, true, snapshot);  // TODO:  is this appropriate to do inside the monitor?
          }

          var chng = pt.TagsChanged;
          if (chng != null) {
            chng(this, new SnapshotSpanEventArgs(new SnapshotSpan(snapshot, 0, snapshot.Length)));
          }
        }
      }
    }

    public event EventHandler<SnapshotSpanEventArgs> TagsChanged;
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
      NormalizedSnapshotSpanCollection chs;
      chs = new NormalizedSnapshotSpanCollection(Map(pre, span => span.TranslateTo(targetSnapshot, SpanTrackingMode.EdgeExclusive)));
      foreach (SnapshotSpan span in NormalizedSnapshotSpanCollection.Overlap(spans, chs)) {
        yield return new TagSpan<ProgressGlyphTag>(span, new ProgressGlyphTag(0));
      }
      chs = new NormalizedSnapshotSpanCollection(Map(post, span => span.TranslateTo(targetSnapshot, SpanTrackingMode.EdgeExclusive)));
      foreach (SnapshotSpan span in NormalizedSnapshotSpanCollection.Overlap(spans, chs)) {
        yield return new TagSpan<ProgressGlyphTag>(span, new ProgressGlyphTag(1));
      }
    }

    /// <summary>
    /// (Why the firetruck isn't an extension method like this already in the standard library?)
    /// </summary>
    public static IEnumerable<TOut> Map<TIn, TOut>(IEnumerable<TIn> coll, System.Func<TIn, TOut> fn) {
      foreach (var e in coll) {
        yield return fn(e);
      }
    }
  }
}
