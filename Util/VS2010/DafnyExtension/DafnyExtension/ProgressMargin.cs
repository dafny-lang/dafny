using System;
using System.Collections.Generic;
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
        Fill = dtag.Val == 0 ? Brushes.Goldenrod : Brushes.DarkOrange,
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
        latestProgram = r._program;
        latestSnapshot = latestProgram != null ? r._snapshot : null;
      }
    }

    ITextVersion latestClearedVersion;
    public void DoTheVerification(object sender, EventArgs args) {
      var buffer = sender as ITextBuffer;
      if (buffer != null && latestProgram != null) {
        bufferChangesPreVerificationStart.AddRange(bufferChangesPostVerificationStart);
        bufferChangesPostVerificationStart.Clear();

        // do the verification
        var newErrors = new List<DafnyError>();
        bool success = DafnyDriver.Verify(latestProgram, (errorInfo) => {
          newErrors.Add(new DafnyError(errorInfo.Tok.line - 1, errorInfo.Tok.col - 1, ErrorCategory.VerificationError, errorInfo.Msg));
          foreach (var aux in errorInfo.Aux) {
            newErrors.Add(new DafnyError(aux.Tok.line - 1, aux.Tok.col - 1, ErrorCategory.AuxInformation, aux.Msg));
          }
        });

        bufferChangesPreVerificationStart.Clear();  // note, depending on concurrency, there may now be more things in the ...Post... list
        if (resolver != null) {
          resolver.PopulateErrorList(newErrors, true, latestSnapshot);
        }

        // What the Error List now reports reflects the latest verification
        var chng = TagsChanged;
        if (chng != null) {
          var snap = latestSnapshot;
          latestClearedVersion = snap.Version;
          chng(this, new SnapshotSpanEventArgs(new SnapshotSpan(snap, 0, snap.Length)));
        }
      }
    }

    public event EventHandler<SnapshotSpanEventArgs> TagsChanged;
    IEnumerable<ITagSpan<ProgressGlyphTag>> ITagger<ProgressGlyphTag>.GetTags(NormalizedSnapshotSpanCollection spans) {
      if (spans.Count == 0) yield break;
      var targetSnapshot = spans[0].Snapshot;

      // If the requested snapshot isn't the same as the one our words are on, translate our spans to the expected snapshot
      NormalizedSnapshotSpanCollection chs;
      chs = new NormalizedSnapshotSpanCollection(Map(bufferChangesPreVerificationStart, span => span.TranslateTo(targetSnapshot, SpanTrackingMode.EdgeExclusive)));
      foreach (SnapshotSpan span in NormalizedSnapshotSpanCollection.Overlap(spans, chs)) {
        yield return new TagSpan<ProgressGlyphTag>(span, new ProgressGlyphTag(0));
      }
      chs = new NormalizedSnapshotSpanCollection(Map(bufferChangesPostVerificationStart, span => span.TranslateTo(targetSnapshot, SpanTrackingMode.EdgeExclusive)));
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
