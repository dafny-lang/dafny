using System;
using System.Collections.Generic;
using System.Linq;
using System.ComponentModel.Composition;
using Microsoft.VisualStudio.Text;
using Microsoft.VisualStudio.Text.Classification;
using Microsoft.VisualStudio.Text.Editor;
using Microsoft.VisualStudio.Text.Tagging;
using Microsoft.VisualStudio.Utilities;
using Dafny = Microsoft.Dafny;

namespace DafnyLanguage
{
  [Export(typeof(ITaggerProvider))]
  [ContentType("dafny")]
  [TagType(typeof(DafnyTokenTag))]
  internal sealed class DafnyTokenTagProvider : ITaggerProvider
  {
    public ITagger<T> CreateTagger<T>(ITextBuffer buffer) where T : ITag {
      return new DafnyTokenTagger(buffer) as ITagger<T>;
    }
  }

  public enum DafnyTokenKinds
  {
    Keyword, Number, String, Comment,
    TypeIdentifier, VariableIdentifier
  }

  public class DafnyTokenTag : ITag
  {
    public DafnyTokenKinds Kind { get; private set; }

    public DafnyTokenTag(DafnyTokenKinds kind) {
      this.Kind = kind;
    }
  }
  public class IdentifierDafnyTokenTag : DafnyTokenTag
  {
    public IdentifierDafnyTokenTag()
      : base(DafnyTokenKinds.VariableIdentifier) {
    }
  }
  public class TypeDafnyTokenTag : DafnyTokenTag
  {
    public TypeDafnyTokenTag()
      : base(DafnyTokenKinds.TypeIdentifier) {
    }
  }

  internal sealed class DafnyTokenTagger : ITagger<DafnyTokenTag>
  {
    ITextBuffer _buffer;
    ITextSnapshot _snapshot;
    List<DRegion> _regions;

    internal DafnyTokenTagger(ITextBuffer buffer) {
      _buffer = buffer;
      _snapshot = buffer.CurrentSnapshot;
      _regions = Rescan(_snapshot);

      _buffer.Changed += new EventHandler<TextContentChangedEventArgs>(ReparseFile);
    }

    public event EventHandler<SnapshotSpanEventArgs> TagsChanged;
    
    public IEnumerable<ITagSpan<DafnyTokenTag>> GetTags(NormalizedSnapshotSpanCollection spans) {
      if (spans.Count == 0)
        yield break;

      List<DRegion> currentRegions = _regions;
      ITextSnapshot currentSnapshot = _snapshot;

      // create a new SnapshotSpan for the entire region encompassed by the span collection
      SnapshotSpan entire = new SnapshotSpan(spans[0].Start, spans[spans.Count - 1].End).TranslateTo(currentSnapshot, SpanTrackingMode.EdgeExclusive);
      int startLineNumber = entire.Start.GetContainingLine().LineNumber;
      int endLineNumber = entire.End.GetContainingLine().LineNumber;
      
      // return tags for any regions that fall within that span
      // BUGBUG: depending on how GetTags gets called (e.g., once for each line in the buffer), this may produce quadratic behavior
      foreach (var region in currentRegions) {
        if (entire.IntersectsWith(region.Span)) {
          // BUGBUG: this returns a span for currentSnapshot, but shouldn't we return spans for the spans[0].Snapshot?
          yield return new TagSpan<DafnyTokenTag>(new SnapshotSpan(region.Start, region.End), new DafnyTokenTag(region.Kind));
        }
      }
    }

    /// <summary>
    /// Find all of the tag regions in the document (snapshot) and notify
    /// listeners of any that changed
    /// </summary>
    void ReparseFile(object sender, TextContentChangedEventArgs args) {
      ITextSnapshot snapshot = _buffer.CurrentSnapshot;
      if (snapshot == _snapshot)
        return;  // we've already computed the regions for this snapshot
       
      // get all of the outline regions in the snapshot
      List<DRegion> newRegions = Rescan(snapshot);

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

    private static List<DRegion> Rescan(ITextSnapshot newSnapshot) {
      List<DRegion> newRegions = new List<DRegion>();

      bool stillScanningLongComment = false;
      SnapshotPoint commentStart = new SnapshotPoint();  // used only when stillScanningLongComment
      SnapshotPoint commentEndAsWeKnowIt = new SnapshotPoint();  // used only when stillScanningLongComment
      foreach (ITextSnapshotLine line in newSnapshot.Lines) {
        string txt = line.GetText();  // the current line (without linebreak characters)
        int N = txt.Length;  // length of the current line 
        int cur = 0;  // offset into the current line

        if (stillScanningLongComment) {
          if (ScanForEndOfComment(txt, ref cur)) {
            newRegions.Add(new DRegion(commentStart, new SnapshotPoint(newSnapshot, line.Start + cur), DafnyTokenKinds.Comment));
            stillScanningLongComment = false;
          } else {
            commentEndAsWeKnowIt = new SnapshotPoint(newSnapshot, line.Start + cur);
          }
        }

        // repeatedly get the remaining tokens from this line
        int end;  // offset into the current line
        for (; ; cur = end) {
          // advance to the first character of a keyword or token
          DafnyTokenKinds ty = DafnyTokenKinds.Keyword;
          for (; ; cur++) {
            if (N <= cur) {
              // we've looked at everything in this line
              goto OUTER_CONTINUE;
            }
            char ch = txt[cur];
            if ('a' <= ch && ch <= 'z') break;
            if ('A' <= ch && ch <= 'Z') break;
            if ('0' <= ch && ch <= '9') { ty = DafnyTokenKinds.Number; break; }
            if (ch == '"') { ty = DafnyTokenKinds.String; break; }
            if (ch == '/') { ty = DafnyTokenKinds.Comment; break; }
            if (ch == '\'' || ch == '_' || ch == '?' || ch == '\\') break;  // parts of identifiers
          }

          // advance to the end of the token
          end = cur + 1;  // offset into the current line
          if (ty == DafnyTokenKinds.Number) {
            // scan the rest of this number
            for (; end < N; end++) {
              char ch = txt[end];
              if ('0' <= ch && ch <= '9') {
              } else break;
            }
          } else if (ty == DafnyTokenKinds.String) {
            // scan the rest of this string, but not past the end-of-line
            for (; end < N; end++) {
              char ch = txt[end];
              if (ch == '"') {
                end++; break;
              } else if (ch == '\\') {
                // escape sequence
                end++;
                if (end == N) { break; }
                ch = txt[end];
                if (ch == 'u') {
                  end += 4;
                  if (N <= end) { end = N; break; }
                }
              }
            }
          } else if (ty == DafnyTokenKinds.Comment) {
            if (end == N) continue;  // this was not the start of a comment
            char ch = txt[end];
            if (ch == '/') {
              // a short comment
              end = N;
            } else if (ch == '*') {
              // a long comment; find the matching "*/"
              end++;
              commentStart = new SnapshotPoint(newSnapshot, line.Start + cur);
              if (ScanForEndOfComment(txt, ref end)) {
                newRegions.Add(new DRegion(commentStart, new SnapshotPoint(newSnapshot, line.Start + end), DafnyTokenKinds.Comment));
              } else {
                stillScanningLongComment = true;
                commentEndAsWeKnowIt = new SnapshotPoint(newSnapshot, line.Start + end);
              }
              continue;
            } else {
              // not a comment
              continue;
            }
          } else {
            int trailingDigits = 0;
            for (; end < N; end++) {
              char ch = txt[end];
              if ('a' <= ch && ch <= 'z') {
                trailingDigits = 0;
              } else if ('A' <= ch && ch <= 'Z') {
                trailingDigits = 0;
              } else if ('0' <= ch && ch <= '9') {
                trailingDigits++;
              } else if (ch == '\'' || ch == '_' || ch == '?' || ch == '\\') {
                trailingDigits = 0;
              } else break;
            }
            // we have a keyword or an identifier
            string s = txt.Substring(cur, end - cur);
            if (0 < trailingDigits && s.Length == 5 + trailingDigits && s.StartsWith("array") && s[5] != '0' && s != "array1") {
              // this is a keyword (array2, array3, ...)
            } else {
              switch (s) {
                #region keywords
                case "allocated":
                case "array":
                case "assert":
                case "assume":
                case "bool":
                case "break":
                case "by":
                case "case":
                case "choose":
                case "class":
                case "constructor":
                case "datatype":
                case "decreases":
                case "else":
                case "ensures":
                case "exists":
                case "false":
                case "forall":
                case "foreach":
                case "free":
                case "fresh":
                case "function":
                case "ghost":
                case "havoc":
                case "if":
                case "imports":
                case "in":
                case "int":
                case "invariant":
                case "label":
                case "match":
                case "method":
                case "modifies":
                case "module":
                case "nat":
                case "new":
                case "null":
                case "object":
                case "old":
                case "print":
                case "reads":
                case "refines":
                case "replaces":
                case "requires":
                case "result":
                case "return":
                case "returns":
                case "seq":
                case "set":
                case "static":
                case "then":
                case "this":
                case "true":
                case "unlimited":
                case "var":
                case "while":
                #endregion
                  break;
                default:
                  continue;  // it was an identifier
              }
            }
          }

          newRegions.Add(new DRegion(new SnapshotPoint(newSnapshot, line.Start + cur), new SnapshotPoint(newSnapshot, line.Start + end), ty));
        }
      OUTER_CONTINUE: ;
      }

      if (stillScanningLongComment) {
        newRegions.Add(new DRegion(commentStart, commentEndAsWeKnowIt, DafnyTokenKinds.Comment));
      }

      return newRegions;
    }

    private static bool ScanForEndOfComment(string txt, ref int end) {
      int N = txt.Length;
      for (; end < N; end++) {
        char ch = txt[end];
        if (ch == '*' && end + 1 < N) {
          ch = txt[end + 1];
          if (ch == '/') {
            end += 2;
            return true;
          }
        }
      }
      return false;  // hit end-of-line without finding end-of-comment
    }
  }

  internal class DRegion
  {
    public SnapshotPoint Start { get; private set; }
    public SnapshotPoint End { get; private set; }
    public SnapshotSpan Span {
      get { return new SnapshotSpan(Start, End); }
    }
    public DafnyTokenKinds Kind { get; private set; }

    public DRegion(SnapshotPoint start, SnapshotPoint end, DafnyTokenKinds kind) {
      Start = start;
      End = end;
      Kind = kind;
    }
  }
}
