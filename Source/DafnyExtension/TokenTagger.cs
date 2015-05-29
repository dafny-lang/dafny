using System;
using System.Collections.Generic;
using System.ComponentModel.Composition;
using System.Linq;
using Microsoft.VisualStudio.Text;
using Microsoft.VisualStudio.Text.Tagging;
using Microsoft.VisualStudio.Utilities;
using System.Diagnostics.Contracts;


namespace DafnyLanguage
{

  #region Provider

  [Export(typeof(ITaggerProvider))]
  [ContentType("dafny")]
  [TagType(typeof(DafnyTokenTag))]
  internal sealed class DafnyTokenTagProvider : ITaggerProvider
  {
    public ITagger<T> CreateTagger<T>(ITextBuffer buffer) where T : ITag {
      return new DafnyTokenTagger(buffer) as ITagger<T>;
    }
  }

  #endregion


  #region Tagger

  public enum DafnyTokenKind
  {
    Keyword, Number, String, Comment,
    VariableIdentifier, VariableIdentifierDefinition,
    AdditionalInformation
  }

  public class DafnyTokenTag : ITag
  {
    string FixedHoverText;
    private Microsoft.Dafny.IVariable Variable;
    public DafnyTokenKind Kind { get; private set; }
    public string HoverText
    {
      get
      {
        string text = FixedHoverText;
        if (Variable != null && Variable.HasBeenAssignedUniqueName)
        {
          bool wasUpdated;
          var value = DafnyClassifier.DafnyMenuPackage.TryToLookupValueInCurrentModel(Variable.UniqueName, out wasUpdated);
          if (value != null)
          {
            text = string.Format("{0} ({1}value = {2})", text == null ? "" : text, wasUpdated ? "new " : "", value);
          }
        }
        return text;
      }
    }

    public DafnyTokenTag(DafnyTokenKind kind) {
      this.Kind = kind;
    }

    public DafnyTokenTag(DafnyTokenKind kind, string fixedHoverText, Microsoft.Dafny.IVariable variable = null)
    {
      this.Kind = kind;
      this.FixedHoverText = fixedHoverText;
      this.Variable = variable;
    }
  }

  internal sealed class DafnyTokenTagger : ITagger<DafnyTokenTag>, IDisposable
  {
    ITextBuffer _buffer;
    ITextSnapshot _snapshot;
    List<TokenRegion> _regions;
    bool _disposed;

    internal DafnyTokenTagger(ITextBuffer buffer) {
      _buffer = buffer;
      _snapshot = buffer.CurrentSnapshot;
      _regions = Rescan(_snapshot);

      _buffer.Changed += new EventHandler<TextContentChangedEventArgs>(ReparseFile);
    }

    public void Dispose() {
      lock (this) {
        if (!_disposed) {
          _buffer.Changed -= ReparseFile;
          _buffer = null;
          _snapshot = null;
          _regions = null;
          _disposed = true;
        }
      }
      GC.SuppressFinalize(this);
    }

    public event EventHandler<SnapshotSpanEventArgs> TagsChanged;

    public IEnumerable<ITagSpan<DafnyTokenTag>> GetTags(NormalizedSnapshotSpanCollection spans) {
      if (spans.Count == 0)
        yield break;

      List<TokenRegion> currentRegions = _regions;
      ITextSnapshot currentSnapshot = _snapshot;

      // create a new SnapshotSpan for the entire region encompassed by the span collection
      SnapshotSpan entire = new SnapshotSpan(spans[0].Start, spans[spans.Count - 1].End).TranslateTo(currentSnapshot, SpanTrackingMode.EdgeExclusive);

      // return tags for any regions that fall within that span
      // BUGBUG: depending on how GetTags gets called (e.g., once for each line in the buffer), this may produce quadratic behavior
      foreach (var region in currentRegions) {
        if (entire.IntersectsWith(region.Span)) {
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
      List<TokenRegion> newRegions = Rescan(snapshot);

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

      var chng = TagsChanged;
      if (chng != null) {
        foreach (var span in difference) {
          chng(this, new SnapshotSpanEventArgs(span));
        }
      }
    }

    static NormalizedSnapshotSpanCollection SymmetricDifference(NormalizedSnapshotSpanCollection first, NormalizedSnapshotSpanCollection second) {
      return NormalizedSnapshotSpanCollection.Union(
          NormalizedSnapshotSpanCollection.Difference(first, second),
          NormalizedSnapshotSpanCollection.Difference(second, first));
    }

    private static List<TokenRegion> Rescan(ITextSnapshot newSnapshot) {
      List<TokenRegion> newRegions = new List<TokenRegion>();

      int longCommentDepth = 0;
      SnapshotPoint commentStart = new SnapshotPoint();  // used only when longCommentDepth != 0
      SnapshotPoint commentEndAsWeKnowIt = new SnapshotPoint();  // used only when longCommentDepth != 0
      foreach (ITextSnapshotLine line in newSnapshot.Lines) {
        string txt = line.GetText();  // the current line (without linebreak characters)
        int N = txt.Length;  // length of the current line
        int cur = 0;  // offset into the current line

        if (longCommentDepth != 0) {
          ScanForEndOfComment(txt, ref longCommentDepth, ref cur);
          if (longCommentDepth == 0) {
            // we just finished parsing a long comment
            newRegions.Add(new TokenRegion(commentStart, new SnapshotPoint(newSnapshot, line.Start + cur), DafnyTokenKind.Comment));
          } else {
            // we're still parsing the long comment
            Contract.Assert(cur == txt.Length);
            commentEndAsWeKnowIt = new SnapshotPoint(newSnapshot, line.Start + cur);
            goto OUTER_CONTINUE;
          }
        }

        // repeatedly get the remaining tokens from this line
        int end;  // offset into the current line
        for (; ; cur = end) {
          // advance to the first character of a keyword or token
          DafnyTokenKind ty = DafnyTokenKind.Keyword;
          for (; ; cur++) {
            if (N <= cur) {
              // we've looked at everything in this line
              goto OUTER_CONTINUE;
            }
            char ch = txt[cur];
            if ('a' <= ch && ch <= 'z') break;
            if ('A' <= ch && ch <= 'Z') break;
            if ('0' <= ch && ch <= '9') { ty = DafnyTokenKind.Number; break; }
            if (ch == '\'' || ch == '_' || ch == '?' || ch == '\\') break;  // parts of identifiers
            if (ch == '"') { ty = DafnyTokenKind.String; break; }
            if (ch == '/') { ty = DafnyTokenKind.Comment; break; }
          }

          // advance to the end of the token
          end = cur + 1;  // offset into the current line
          if (ty == DafnyTokenKind.Number) {
            // scan the rest of this number
            for (; end < N; end++) {
              char ch = txt[end];
              if ('0' <= ch && ch <= '9') {
              } else break;
            }
          } else if (ty == DafnyTokenKind.String) {
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
          } else if (ty == DafnyTokenKind.Comment) {
            if (end == N) continue;  // this was not the start of a comment; it was just a single "/" and we don't care to color it
            char ch = txt[end];
            if (ch == '/') {
              // a short comment
              end = N;
            } else if (ch == '*') {
              // a long comment; find the matching "*/"
              end++;
              commentStart = new SnapshotPoint(newSnapshot, line.Start + cur);
              Contract.Assert(longCommentDepth == 0);
              longCommentDepth = 1;
              ScanForEndOfComment(txt, ref longCommentDepth, ref end);
              if (longCommentDepth == 0) {
                // we finished scanning a long comment, and "end" is set to right after it
                newRegions.Add(new TokenRegion(commentStart, new SnapshotPoint(newSnapshot, line.Start + end), DafnyTokenKind.Comment));
              } else {
                commentEndAsWeKnowIt = new SnapshotPoint(newSnapshot, line.Start + end);
              }
              continue;
            } else {
              // not a comment; it was just a single "/" and we don't care to color it
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
            if (0 < trailingDigits && s.Length == 5 + trailingDigits && s.StartsWith("array") && s[5] != '0' && (trailingDigits != 1 || s[5] != '1')) {
              // this is a keyword (array2, array3, ...)
            } else {
              switch (s) {
                #region keywords
                case "abstract":
                case "array":
                case "as":
                case "assert":
                case "assume":
                case "bool":
                case "break":
                case "calc":
                case "case":
                case "char":
                case "class":
                case "trait":
                case "extends":
                case "codatatype":
                case "colemma":
                case "constructor":
                case "copredicate":
                case "datatype":
                case "decreases":
                case "default":
                case "else":
                case "ensures":
                case "exists":
                case "false":
                case "forall":
                case "free":
                case "fresh":
                case "function":
                case "ghost":
                case "if":
                case "imap":
                case "iset":
                case "import":
                case "in":
                case "include":
                case "inductive":
                case "int":
                case "invariant":
                case "iterator":
                case "label":
                case "lemma":
                case "map":
                case "match":
                case "method":
                case "modifies":
                case "modify":
                case "module":
                case "multiset":
                case "nat":
                case "new":
                case "newtype":
                case "null":
                case "object":
                case "old":
                case "opened":
                case "predicate":
                case "print":
                case "protected":
                case "reads":
                case "real":
                case "refines":
                case "requires":
                case "return":
                case "returns":
                case "seq":
                case "set":
                case "static":
                case "string":
                case "then":
                case "this":
                case "true":
                case "type":
                case "var":
                case "where":
                case "while":
                case "yield":
                case "yields":
                #endregion
                  break;
                default:
                  continue;  // it was an identifier, so we don't color it
              }
            }
          }

          newRegions.Add(new TokenRegion(new SnapshotPoint(newSnapshot, line.Start + cur), new SnapshotPoint(newSnapshot, line.Start + end), ty));
        }
      OUTER_CONTINUE: ;
      }

      if (longCommentDepth != 0) {
        // This was a malformed comment, running to the end of the buffer.  Above, we let "commentEndAsWeKnowIt" be the end of the
        // last line, so we can use it here.
        newRegions.Add(new TokenRegion(commentStart, commentEndAsWeKnowIt, DafnyTokenKind.Comment));
      }

      return newRegions;
    }

    /// <summary>
    /// Scans "txt" beginning with depth "depth", which is assumed to be non-0.  Any occurrences of "/*" or "*/"
    /// increment or decrement "depth".  If "depth" ever reaches 0, then "end" returns as the number of characters
    /// consumed from "txt" (including the last "*/").  If "depth" is still non-0 when the entire "txt" has
    /// been consumed, then "end" returns as the length of "txt".  (Note, "end" may return as the length of "txt"
    /// if "depth" is still non-0 or if "depth" became 0 from reading the last characters of "txt".)
    /// </summary>
    private static void ScanForEndOfComment(string txt, ref int depth, ref int end) {
      Contract.Requires(depth > 0);

      int Nminus1 = txt.Length - 1;  // no reason ever to look at the last character of the line, unless the second-to-last character is '*' or '/'
      for (; end < Nminus1; ) {
        char ch = txt[end];
        if (ch == '*' && txt[end + 1] == '/') {
          end += 2;
          depth--;
          if (depth == 0) { return; }
        } else if (ch == '/' && txt[end + 1] == '*') {
          end += 2;
          depth++;
        } else {
          end++;
        }
      }
      end = txt.Length;  // we didn't look at the last character, but we still consumed all the output
    }
  }

  internal class TokenRegion
  {
    public SnapshotPoint Start { get; private set; }
    public SnapshotPoint End { get; private set; }
    public SnapshotSpan Span {
      get { return new SnapshotSpan(Start, End); }
    }
    public DafnyTokenKind Kind { get; private set; }

    public TokenRegion(SnapshotPoint start, SnapshotPoint end, DafnyTokenKind kind) {
      Start = start;
      End = end;
      Kind = kind;
    }
  }

  #endregion

}
