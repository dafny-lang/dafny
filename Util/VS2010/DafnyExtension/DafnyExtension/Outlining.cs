using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Text.RegularExpressions;
using System.Windows.Threading;
using System.ComponentModel.Composition;
using Microsoft.VisualStudio.Text.Outlining;
using Microsoft.VisualStudio.Text.Tagging;
using Microsoft.VisualStudio.Utilities;
using Microsoft.VisualStudio.Text;

namespace DafnyLanguage
{
#if THIS_IS_THE_PAST
  [Export(typeof(ITaggerProvider))]
  [ContentType("dafny")]
  [TagType(typeof(IOutliningRegionTag))]
  internal sealed class OutliningTaggerProvider : ITaggerProvider
  {
    public ITagger<T> CreateTagger<T>(ITextBuffer buffer) where T : ITag {
      // create a single tagger for each buffer.
      Func<ITagger<T>> sc = delegate() { return new OutlineTagger(buffer) as ITagger<T>; };
      return buffer.Properties.GetOrCreateSingletonProperty<ITagger<T>>(sc);
    }
  }

  /// <summary>
  /// Data about one outline region
  /// </summary>
  internal class OutlineRegion
  {
    public SnapshotPoint Start { get; set; }
    public SnapshotPoint End { get; set; }
    public SnapshotSpan Span {
      get { return new SnapshotSpan(Start, End); }
    }

    public string HoverText { get; set; }
    public string Label { get; set; }
  }

  internal sealed class OutlineTagger : ITagger<IOutliningRegionTag>
  {
    ITextBuffer _buffer;
    ITextSnapshot _snapshot;
    List<OutlineRegion> _regions;

    public OutlineTagger(ITextBuffer buffer) {
      _buffer = buffer;
      _snapshot = buffer.CurrentSnapshot;
      _regions = new List<OutlineRegion>();

      ReparseFile(null, EventArgs.Empty);

      // listen for changes to the buffer, but don't process until the user stops typing
      BufferIdleEventUtil.AddBufferIdleEventListener(_buffer, ReparseFile);
    }

    public void Dispose() {
      BufferIdleEventUtil.RemoveBufferIdleEventListener(_buffer, ReparseFile);
    }

    public IEnumerable<ITagSpan<IOutliningRegionTag>> GetTags(NormalizedSnapshotSpanCollection spans) {
      if (spans.Count == 0)
        yield break;

      List<OutlineRegion> currentRegions = _regions;
      ITextSnapshot currentSnapshot = _snapshot;

      // create a new SnapshotSpan for the entire region encompassed by the span collection
      SnapshotSpan entire = new SnapshotSpan(spans[0].Start, spans[spans.Count - 1].End).TranslateTo(currentSnapshot, SpanTrackingMode.EdgeExclusive);
      int startLineNumber = entire.Start.GetContainingLine().LineNumber;
      int endLineNumber = entire.End.GetContainingLine().LineNumber;

      // return outline tags for any regions that fall within that span
      foreach (var region in currentRegions) {
        if (entire.IntersectsWith(region.Span)) {
          //the region starts at the beginning of the "{", and goes until the *end* of the line that contains the "}".
          yield return new TagSpan<OutliningRegionTag>(new SnapshotSpan(region.Start, region.End),
            new OutliningRegionTag(false, false, region.Label, region.HoverText));
        }
      }
    }

    public event EventHandler<SnapshotSpanEventArgs> TagsChanged;

    static string ellipsis = "...";    //the characters that are displayed when the region is collapsed
    static Regex matchKey = new Regex("^\\s*(datatype|method|function)");
    static int MaxHiddenLines = 15;
    static char[] eitherBrace = { '{', '}' };

    /// <summary>
    /// Find all of the outline sections in the snapshot
    /// </summary>
    private List<OutlineRegion> ParseOutlineSections(ITextSnapshot newSnapshot) {
      List<OutlineRegion> newRegions = new List<OutlineRegion>();

      // We care about three states:
      // (0) looking for an outlineable declaration
      // (1) have found an outlineable declaration, looking for an open curly
      // (2) looking for a close curly
      // The search used here is not at all exact, and it would be easy to get it to
      // do the wrong thing; however, in common cases, it will do the right thing.
      int state = 0;
      SnapshotPoint start = new SnapshotPoint();  // the value of "start" matters only if state==2
      int braceImbalance = 0;  // used only if state==2
      string hoverText = "";  // used only if state==2
      int hoverLineCount = 0;  // used only if state==2
      string prevLineBreak = "";  // used only if state==2
      foreach (ITextSnapshotLine line in newSnapshot.Lines) {
        string txt = line.GetText();
        if (state == 0) {
          MatchCollection matches = matchKey.Matches(txt);
          if (matches.Count != 0)
            state = 1;
        }
        int startPos = 0;
        if (state == 1) {
          startPos = txt.IndexOf('{');
          if (startPos != -1) {
            start = new SnapshotPoint(newSnapshot, line.Start.Position + startPos + 1);
            startPos++;
            state = 2;
            braceImbalance = 1;
            hoverText = txt.Substring(startPos).Trim();
            hoverLineCount = hoverText.Length == 0 ? 0 : 1;
            prevLineBreak = line.GetLineBreakText();
          }
        }
        if (state == 2) {
          int endPos = startPos;
          while (braceImbalance != 0) {
            endPos = txt.IndexOfAny(eitherBrace, endPos);
            if (endPos == -1) break;
            char ch = txt[endPos];
            if (ch == '{') {
              braceImbalance++;
            } else {
              braceImbalance--;
              if (braceImbalance == 0) break;
            }
            endPos++;
          }

          if (endPos == -1) {
            // not there yet
            if (startPos == 0 && hoverLineCount < MaxHiddenLines) {
              string h = txt.Trim();
              if (h.Length != 0) {
                if (hoverText.Length != 0)
                  hoverText += prevLineBreak;
                hoverText += h;
                hoverLineCount++;
                prevLineBreak = line.GetLineBreakText();
              }
            }
          } else {
            // we found the end
            if (startPos != 0) {
              hoverText = txt.Substring(startPos, endPos - startPos).Trim();
            } else if (hoverLineCount < MaxHiddenLines) {
              string h = txt.Substring(0, endPos).Trim();
              if (h.Length != 0) {
                if (hoverText.Length != 0)
                  hoverText += prevLineBreak;
                hoverText += h;
              }
            }
            SnapshotPoint end = new SnapshotPoint(newSnapshot, line.Start.Position + endPos);
            newRegions.Add(new OutlineRegion() {
              Start = start, End = end, Label = ellipsis,
              HoverText = hoverText
            });
            state = 0;
          }
        }
      }

      return newRegions;
    }

    /// <summary>
    /// Find all of the outline regions in the document (snapshot) and notify
    /// listeners of any that changed
    /// </summary>
    void ReparseFile(object sender, EventArgs args) {
      ITextSnapshot snapshot = _buffer.CurrentSnapshot;

      // get all of the outline regions in the snapshot
      List<OutlineRegion> newRegions = ParseOutlineSections(snapshot);

      // determine the changed span, and send a changed event with the new spans
      List<SnapshotSpan> oldSpans = new List<SnapshotSpan>(_regions.Select(r =>
        r.Span.TranslateTo(snapshot, SpanTrackingMode.EdgeExclusive)));

      List<SnapshotSpan> newSpans = new List<SnapshotSpan>(newRegions.Select(r => r.Span));

      NormalizedSnapshotSpanCollection oldSpanCollection = new NormalizedSnapshotSpanCollection(oldSpans);
      NormalizedSnapshotSpanCollection newSpanCollection = new NormalizedSnapshotSpanCollection(newSpans);

      NormalizedSnapshotSpanCollection difference = SymmetricDifference(oldSpanCollection, newSpanCollection);

      // save the new baseline
      _snapshot = snapshot;
      _regions = newRegions;

      foreach (var span in difference) {
        var chng = TagsChanged;
        if (chng != null)
          chng(this, new SnapshotSpanEventArgs(span));
      }
    }

    NormalizedSnapshotSpanCollection SymmetricDifference(NormalizedSnapshotSpanCollection first, NormalizedSnapshotSpanCollection second) {
      return NormalizedSnapshotSpanCollection.Union(
          NormalizedSnapshotSpanCollection.Difference(first, second),
          NormalizedSnapshotSpanCollection.Difference(second, first));
    }
  }
#endif
}
