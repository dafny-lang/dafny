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
using Microsoft.VisualStudio.Utilities;
using System.Diagnostics.Contracts;


namespace DafnyLanguage
{
  internal class ProgressMarginGlyphFactory : IGlyphFactory
  {
    const double m_glyphSize = 16.0;

    public UIElement GenerateGlyph(IWpfTextViewLine line, IGlyphTag tag) {
      var dtag = tag as ProgressGlyphTag;
      if (dtag == null) {
        return null;
      }

      System.Windows.Shapes.Ellipse ellipse = new Ellipse();
      ellipse.Fill = Brushes.LightBlue;
      ellipse.StrokeThickness = 2;
      ellipse.Stroke = dtag.V == 0 ? Brushes.DarkBlue : Brushes.BlanchedAlmond;
      ellipse.Height = m_glyphSize;
      ellipse.Width = m_glyphSize;

      return ellipse;
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
    public int V;
    public ProgressGlyphTag(int v) {
      V = v;
    }
  }

  internal class ProgressTagger : ITagger<ProgressGlyphTag>
  {
    public ProgressTagger(ITextBuffer buffer) {
      BufferIdleEventUtil.AddBufferIdleEventListener(buffer, ClearMarks);
    }

    ITextVersion latestClearedVersion;

    public void ClearMarks(object sender, EventArgs args) {
      var buffer = sender as ITextBuffer;
      var chng = TagsChanged;
      if (buffer != null && chng != null) {
        var snap = buffer.CurrentSnapshot;
        latestClearedVersion = snap.Version;
        chng(this, new SnapshotSpanEventArgs(new SnapshotSpan(snap, 0, snap.Length)));
      }
    }

    IEnumerable<ITagSpan<ProgressGlyphTag>> ITagger<ProgressGlyphTag>.GetTags(NormalizedSnapshotSpanCollection spans) {
      if (spans.Count == 0) yield break;
      if (spans[0].Snapshot.Version != latestClearedVersion) {
        foreach (SnapshotSpan span in spans) {
          yield return new TagSpan<ProgressGlyphTag>(new SnapshotSpan(span.Start, span.Length), new ProgressGlyphTag(1));
        }
      }
    }
    public event EventHandler<SnapshotSpanEventArgs> TagsChanged;
  }

  [Export(typeof(ITaggerProvider))]
  [ContentType("dafny")]
  [TagType(typeof(ProgressGlyphTag))]
  class ProgressTaggerProvider : ITaggerProvider
  {
    public ITagger<T> CreateTagger<T>(ITextBuffer buffer) where T : ITag {
      return new ProgressTagger(buffer) as ITagger<T>;
    }
  }
}
