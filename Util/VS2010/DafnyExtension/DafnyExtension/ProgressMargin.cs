using System;
using System.Collections.Generic;
using System.Threading;
using System.Windows.Threading;
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

    readonly DispatcherTimer timer;

    public ProgressTagger(ITextBuffer buffer, IServiceProvider serviceProvider, ITagAggregator<DafnyResolverTag> tagAggregator) {
      _buffer = buffer;
      _errorProvider = new ErrorListProvider(serviceProvider);

      timer = new DispatcherTimer(DispatcherPriority.ApplicationIdle);
      timer.Interval = TimeSpan.FromMilliseconds(500);
      timer.Tick += new EventHandler(UponIdle);

      tagAggregator.TagsChanged += new EventHandler<TagsChangedEventArgs>(_aggregator_TagsChanged);
      buffer.Changed += new EventHandler<TextContentChangedEventArgs>(buffer_Changed);
      bufferChangesPostVerificationStart.Add(new SnapshotSpan(buffer.CurrentSnapshot, 0, buffer.CurrentSnapshot.Length));
    }

    public void Dispose() {
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
    /// <summary>
    /// This method is invoked when the user has been idle for a little while.
    /// Note, "sender" and "args" are allowed to be passed in as null--they are not used by this method.
    /// </summary>
    public void UponIdle(object sender, EventArgs args) {
      Dafny.Program prog;
      ITextSnapshot snap;
      ResolverTagger r;
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
        r = resolver;
        resolver = null;
        if (prog == null) return;
        // We have a successfully resolved program to verify

        var resolvedVersion = snap.Version.VersionNumber;
        if (!bufferChangesPostVerificationStart.TrueForAll(span => span.Snapshot.Version.VersionNumber <= resolvedVersion)) {
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
        var chng = TagsChanged;
        if (chng != null) {
          chng(this, new SnapshotSpanEventArgs(new SnapshotSpan(snap, 0, snap.Length)));
        }

      }
      new Thread(() => VerificationWorker(prog, snap, r)).Start();
    }

    /// <summary>
    /// Thread entry point.
    /// </summary>
    void VerificationWorker(Dafny.Program program, ITextSnapshot snapshot, ResolverTagger errorListHolder) {
      Contract.Requires(program != null);
      Contract.Requires(snapshot != null);
      Contract.Requires(errorListHolder != null);

      // Run the verifier
      var newErrors = new List<DafnyError>();
      bool success = DafnyDriver.Verify(program, errorInfo => {
        newErrors.Add(new DafnyError(errorInfo.Tok.line - 1, errorInfo.Tok.col - 1, ErrorCategory.VerificationError, errorInfo.Msg));
        foreach (var aux in errorInfo.Aux) {
          newErrors.Add(new DafnyError(aux.Tok.line - 1, aux.Tok.col - 1, ErrorCategory.AuxInformation, aux.Msg));
        }
      });
      errorListHolder.PopulateErrorList(newErrors, true, snapshot);

      lock (this) {
        bufferChangesPreVerificationStart.Clear();
        verificationInProgress = false;
      }
      // Notify to-whom-it-may-concern about the cleared pre-verification changes
      var chng = TagsChanged;
      if (chng != null) {
        chng(this, new SnapshotSpanEventArgs(new SnapshotSpan(snapshot, 0, snapshot.Length)));
      }

      // If new changes took place since we started the verification, we may need to kick off another verification
      // immediately.
      UponIdle(null, null);
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
