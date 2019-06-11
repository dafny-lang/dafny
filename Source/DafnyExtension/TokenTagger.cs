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
    Keyword, SpecificationClause, BuiltInType, Number, String, Char, Comment,
    VariableIdentifier, VariableIdentifierDefinition,
    AdditionalInformation, Attribute, RecognizedAttributeId
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
    internal sealed class ScanResult
    {
      internal ITextSnapshot _oldSnapshot;
      internal ITextSnapshot _newSnapshot;
      internal List<TokenRegion> _regions; // the regions computed for the _newSnapshot
      internal NormalizedSnapshotSpanCollection _difference; // the difference between _oldSnapshot and _newSnapshot

      internal ScanResult(ITextSnapshot oldSnapshot, ITextSnapshot newSnapshot, List<TokenRegion> regions, NormalizedSnapshotSpanCollection diffs) {
        _oldSnapshot = oldSnapshot;
        _newSnapshot = newSnapshot;
        _regions = regions;
        _difference = diffs;
      }
    }

    ITextBuffer _buffer;
    ITextSnapshot _snapshot;
    List<TokenRegion> _regions;
    static object bufferTokenTaggerKey = new object();
    bool _disposed;

    internal DafnyTokenTagger(ITextBuffer buffer) {
      _buffer = buffer;
      _snapshot = buffer.CurrentSnapshot;
      _regions = Scan(_snapshot);

      _buffer.Changed += new EventHandler<TextContentChangedEventArgs>(ReparseFile);
    }

    public void Dispose() {
      lock (this) {
        if (!_disposed) {
          _buffer.Changed -= ReparseFile;
          _buffer.Properties.RemoveProperty(bufferTokenTaggerKey);
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

      NormalizedSnapshotSpanCollection difference = new NormalizedSnapshotSpanCollection();
      ScanResult result;
      if (_buffer.Properties.TryGetProperty(bufferTokenTaggerKey, out result) &&
          (result._oldSnapshot == _snapshot) &&
          (result._newSnapshot == snapshot)) {
        difference = result._difference;
        // save the new baseline
        _regions = result._regions;
        _snapshot = snapshot;
      } else {
        List<TokenRegion>  regions = new List<TokenRegion>();
        List<SnapshotSpan> rescannedRegions = new List<SnapshotSpan>();

        // loop through the changes and check for changes in comments first. If
        // the change is in a comments, we need to rescan starting from the
        // beginning of the comments (which in multi-lined comments, it can
        // be a line that the changes are not on), otherwise, we can just rescan the lines
        // that the changes are on.
        bool done;
        SnapshotPoint start, end;
        for (int i = 0; i < args.Changes.Count; i++) {
          done = false;
          // get the span of the lines that the change is on.
          int cStart = args.Changes[i].NewSpan.Start;
          int cEnd = args.Changes[i].NewSpan.End;
          start = snapshot.GetLineFromPosition(cStart).Start;
          end = snapshot.GetLineFromPosition(cEnd).End;
          SnapshotSpan newSpan = new SnapshotSpan(start, end);
          foreach (TokenRegion r in _regions) {
            if (r.Kind == DafnyTokenKind.Comment) {
              // if the change is in the comments, we want to start scanning from the
              // the beginning of the comments instead.
              SnapshotSpan span = r.Span.TranslateTo(snapshot, SpanTrackingMode.EdgeExclusive);
              if (span.IntersectsWith(newSpan)) {
                start = span.Start.Position < newSpan.Start.Position ? span.Start : newSpan.Start;
                end = span.End.Position > newSpan.End.Position ? span.End : newSpan.End;
                end = Scan(snapshot.GetText(new SnapshotSpan(start, end)), start, regions, snapshot);
                // record the regions that we rescanned.
                rescannedRegions.Add(new SnapshotSpan(start, end));
                done = true;
                break;
              }
            }
          }
          if (!done) {
            // scan the lines that the change is on to generate the new regions.
            end = Scan(snapshot.GetText(new SnapshotSpan(start, end)), start, regions, snapshot);
            // record the span that we rescanned.
            rescannedRegions.Add(new SnapshotSpan(start, end));
          }
        }

        List<SnapshotSpan> oldSpans = new List<SnapshotSpan>();
        List<SnapshotSpan> newSpans = new List<SnapshotSpan>();
        // record the newly created spans.
        foreach (TokenRegion r in regions) {
          newSpans.Add(r.Span);
        }
        // loop through the old scan results and remove the ones that
        // are in the regions that are rescanned.
        foreach (TokenRegion r in _regions) {
          SnapshotSpan origSpan = r.Span.TranslateTo(snapshot, SpanTrackingMode.EdgeExclusive);
          bool obsolete = false;
          foreach (SnapshotSpan span in rescannedRegions) {
            if (origSpan.IntersectsWith(span)) {
              oldSpans.Add(span);
              obsolete = true;
              break;
            }
          }
          if (!obsolete) {
            TokenRegion region = new TokenRegion(origSpan.Start, origSpan.End, r.Kind);
            regions.Add(region);
          }
        }

        NormalizedSnapshotSpanCollection oldSpanCollection = new NormalizedSnapshotSpanCollection(oldSpans);
        NormalizedSnapshotSpanCollection newSpanCollection = new NormalizedSnapshotSpanCollection(newSpans);
        difference = SymmetricDifference(oldSpanCollection, newSpanCollection);

        // save the scan result
        _buffer.Properties[bufferTokenTaggerKey] = new ScanResult(_snapshot, snapshot, regions, difference);
        // save the new baseline
        _snapshot = snapshot;
        _regions = regions;
      }

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

    private static SnapshotPoint Scan(string txt, SnapshotPoint start, List<TokenRegion> newRegions, ITextSnapshot newSnapshot) {
      int longCommentDepth = 0;
      SnapshotPoint commentStart = new SnapshotPoint();
      SnapshotPoint commentEndAsWeKnowIt = new SnapshotPoint();  // used only when longCommentDepth != 0
      int N = txt.Length;
      bool done = false;
      while (!done) {
        N = txt.Length;  // length of the current buffer
        int cur = 0;  // offset into the current buffer
        if (longCommentDepth != 0) {
          ScanForEndOfComment(txt, ref longCommentDepth, ref cur);
          if (longCommentDepth == 0) {
            // we just finished parsing a long comment
            newRegions.Add(new TokenRegion(commentStart, new SnapshotPoint(newSnapshot, start + cur), DafnyTokenKind.Comment));
          } else {
            // we're still parsing the long comment
            Contract.Assert(cur == txt.Length);
            commentEndAsWeKnowIt = new SnapshotPoint(newSnapshot, start + cur);
            goto OUTER_CONTINUE;
          }
        }
        // repeatedly get the remaining tokens from this buffer
        int end;  // offset into the current buffer
        for (; ; cur = end) {
          // advance to the first character of a keyword or token
          DafnyTokenKind ty = DafnyTokenKind.Keyword;
          for (; ; cur++) {
            if (N <= cur) {
              // we've looked at everything in this buffer
              goto OUTER_CONTINUE;
            }
            char ch = txt[cur];
            if ('a' <= ch && ch <= 'z') break;
            if ('A' <= ch && ch <= 'Z') break;
            if ('0' <= ch && ch <= '9') { ty = DafnyTokenKind.Number; break; }
            if (ch == '_' || ch == '?' || ch == '\\') break;  // parts of identifiers
            if (ch == '\'') { ty = DafnyTokenKind.Char; break; }  // part character literal or identifier
            if (ch == '"') { ty = DafnyTokenKind.String; break; }
            if (ch == '/') { ty = DafnyTokenKind.Comment; break; }
          }

          // advance to the end of the token
          end = cur + 1;  // offset into the current buffer
          // first investigate if this is really a character literal
          if (ty == DafnyTokenKind.Char) {
            ty = DafnyTokenKind.Keyword;
            // we've seen a starting single-quote already
            if (cur + 3 <= N && txt[cur + 2] == '\'') {
              // Look for a simple character literal, like 'a'
              char cx = txt[cur + 1];
              if (cx != '\'' && cx != '\\' && cx != '\n' && cx != '\r') {
                if (cur + 3 == N) {
                  ty = DafnyTokenKind.Char;
                  end = cur + 3;
                } else {
                  // check if the next character is an identifier character, because then what we've seen was
                  // really just part of that identifier
                  cx = txt[cur + 3];
                  if ('a' <= cx && cx <= 'z') {
                  } else if ('A' <= cx && cx <= 'Z') {
                  } else if ('0' <= cx && cx <= '9') {
                  } else if (cx == '\'' || cx == '_' || cx == '?' || cx == '\\') {
                  } else {
                    ty = DafnyTokenKind.Char;
                    end = cur + 3;
                  }
                }
              }
            } else if (cur + 4 <= N && txt[cur + 1] == '\\' && txt[cur + 3] == '\'') {
              // Look for an escaped character literal, like '\n' (note, a \ cannot be part of an identifier)
              char cx = txt[cur + 2];
              if (cx == '\'' || cx == '\"' || cx == '\\' || cx == '0' || cx == 'n' || cx == 'r' || cx == 't') {
                ty = DafnyTokenKind.Char;
                end = cur + 4;
              }
            } else if (cur + 8 <= N && txt[cur + 1] == '\\' && txt[cur + 2] == 'u' && txt[cur + 7] == '\'') {
              // Look for a unicode character literal, like '\u40fE' (note, a \ cannot be part of an identifier)
              var numberOfHexDigits = 0;
              for (int i = 3; i < 7; i++) {
                char cx = txt[cur + i];
                if (('0' <= cx && cx <= '9') || ('a' <= cx && cx <= 'f') || ('A' <= cx && cx <= 'F')) {
                  numberOfHexDigits++;
                }
              }
              if (numberOfHexDigits == 4) {
                ty = DafnyTokenKind.Char;
                end = cur + 8;
              }
            }
          }

          if (ty == DafnyTokenKind.Number) {
            // scan the rest of this number
            for (; end < N; end++) {
              char ch = txt[end];
              if ('0' <= ch && ch <= '9') {
              } else break;
            }
          } else if (ty == DafnyTokenKind.Char) {
            // we already did the work above
          } else if (ty == DafnyTokenKind.String) {
            // scan the rest of this string, but not past the end-of-buffer
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
              // a short comment, to the end of the line.
              end = newSnapshot.GetLineFromPosition(start + end).End.Position - start;
            } else if (ch == '*') {
              // a long comment; find the matching "*/"
              end++;
              commentStart = new SnapshotPoint(newSnapshot, start + cur);
              Contract.Assert(longCommentDepth == 0);
              longCommentDepth = 1;
              ScanForEndOfComment(txt, ref longCommentDepth, ref end);
              if (longCommentDepth == 0) {
                // we finished scanning a long comment, and "end" is set to right after it
                newRegions.Add(new TokenRegion(commentStart, new SnapshotPoint(newSnapshot, start + end), DafnyTokenKind.Comment));
              } else {
                commentEndAsWeKnowIt = new SnapshotPoint(newSnapshot, start + end);
              }
              continue;
            } else {
              // not a comment; it was just a single "/" and we don't care to color it
              continue;
            }
          } else {
            // In the following, "trailingDigits" is the number of digits just before position "end" or,
            // if "trailingDigits" is positive and "trailingDigitsAreFollowedByQuery" is true, just before
            // position "end-1".
            // The value of "trailingDigitsAreFollowedByQuery" is relevant only if "trailingDigits" is non-0.
            // If "trailingDigits" is 0, the value of "trailingDigitsAreFollowedByQuery" can be anything.
            // (This design means we don't have to update "trailingDigitsAreFollowedByQuery" often in the
            // loop.)
            int trailingDigits = 0;
            bool trailingDigitsAreFollowedByQuery = false;
            for (; end < N; end++) {
              char ch = txt[end];
              if ('a' <= ch && ch <= 'z') {
                trailingDigits = 0;
              } else if ('A' <= ch && ch <= 'Z') {
                trailingDigits = 0;
              } else if ('0' <= ch && ch <= '9') {
                if (trailingDigitsAreFollowedByQuery) {  // note, "trailingDigits" could be 0, but then this still does the right thing
                  trailingDigits = 1; trailingDigitsAreFollowedByQuery = false;
                } else {
                  trailingDigits++;
                }
              } else if (ch == '?') {
                if (trailingDigitsAreFollowedByQuery) {  // note, "trailingDigits" could be 0, but then this still does the right thing
                  trailingDigits = 0;
                } else {
                  trailingDigitsAreFollowedByQuery = true;
                }
              } else if (ch == '\'' || ch == '_' || ch == '\\') {
                trailingDigits = 0;
              } else break;
            }
            // we have a keyword or an identifier
            string s = txt.Substring(cur, end - cur);
            if (0 < trailingDigits && s.Length == 5 + trailingDigits + (trailingDigitsAreFollowedByQuery ? 1 : 0) && s.StartsWith("array") && s[5] != '0' && (trailingDigits != 1 || s[5] != '1')) {
              // this is a keyword for a built-in type (array2, array3, ..., or array2?, array3?, ...)
              ty = DafnyTokenKind.BuiltInType;
            } else if (0 < trailingDigits && !trailingDigitsAreFollowedByQuery && s.Length == 2 + trailingDigits && s.StartsWith("bv") && (s[2] != '0' || trailingDigits == 1)) {
              // this is a keyword for a built-in type (bv0, bv1, ...)
              ty = DafnyTokenKind.BuiltInType;
            } else {
              switch (s) {
                #region keywords
                case "abstract":
                case "allocated":
                case "as":
                case "assert":
                case "assume":
                case "break":
                case "by":
                case "calc":
                case "case":
                case "class":
                case "const":
                case "trait":
                case "extends":
                case "codatatype":
                case "colemma":
                case "constructor":
                case "copredicate":
                case "datatype":
                case "else":
                case "exists":
                case "export":
                case "false":
                case "forall":
                case "fresh":
                case "function":
                case "ghost":
                case "if":
                case "import":
                case "in":
                case "include":
                case "inductive":
                case "iterator":
                case "label":
                case "lemma":
                case "match":
                case "method":
                case "modify":
                case "module":
                case "new":
                case "newtype":
                case "null":
                case "old":
                case "opened":
                case "predicate":
                case "print":
                case "protected":
                case "refines":
                case "return":
                case "returns":
                case "reveal":
                case "static":
                case "then":
                case "this":
                case "true":
                case "twostate":
                case "type":
                case "unchanged":
                case "var":
                case "where":
                case "while":
                case "yield":
                case "yields":
                #endregion
                  break;
                #region keywords in specification clauses
                case "decreases":
                case "ensures":
                case "invariant":
                case "modifies":
                case "provides":
                case "reads":
                case "requires":
                case "reveals":
                case "witness":
                  // "yields" plays a dual role
                #endregion
                  ty = DafnyTokenKind.SpecificationClause;
                  break;
                #region keywords for built-in types
                case "array":
                case "array?":
                case "bool":
                case "char":
                case "imap":
                case "int":
                case "iset":
                case "map":
                case "multiset":
                case "nat":
                case "object":
                case "object?":
                case "ORDINAL":
                case "real":
                case "seq":
                case "set":
                case "string":
                #endregion
                  ty = DafnyTokenKind.BuiltInType;
                  break;
                default:
                  continue;  // it was an identifier, so we don't color it
              }
            }
          }
          newRegions.Add(new TokenRegion(new SnapshotPoint(newSnapshot, start + cur), new SnapshotPoint(newSnapshot, start + end), ty));
        }
      OUTER_CONTINUE:
        done = true;
        if (longCommentDepth != 0) {
          // we need to look into the next line
          ITextSnapshotLine currLine = newSnapshot.GetLineFromPosition(start + N);
          if ((currLine.LineNumber + 1) < newSnapshot.LineCount) {
            ITextSnapshotLine nextLine = newSnapshot.GetLineFromLineNumber(currLine.LineNumber + 1);
            txt = nextLine.GetText();
            start = nextLine.Start;
            // we are done scanning the current buffer, but not the whole file yet.
            // we need to continue to find the enclosing "*/", or until the end of the file.
            done = false;
          } else {
            // This was a malformed comment, running to the end of the buffer.  Above, we let "commentEndAsWeKnowIt" be the end of the
            // last line, so we can use it here.
            newRegions.Add(new TokenRegion(commentStart, commentEndAsWeKnowIt, DafnyTokenKind.Comment));
          }
        }
      }
      return new SnapshotPoint(newSnapshot, start + N);
    }

    private List<TokenRegion> Scan(ITextSnapshot newSnapshot) {
      List<TokenRegion> newRegions;
      ScanResult result;
      if (_buffer.Properties.TryGetProperty(bufferTokenTaggerKey, out result) &&
        result._newSnapshot == newSnapshot) {
        newRegions = result._regions;
      } else {
        newRegions = new List<TokenRegion>();
        int nextLineNumber = -1;
        foreach (ITextSnapshotLine line in newSnapshot.Lines) {
          if (line.LineNumber <= nextLineNumber) {
            // the line is already processed.
            continue;
          }
          string txt = line.GetText();  // the current line (without linebreak characters)
          SnapshotPoint end = Scan(txt, line.Start, newRegions, newSnapshot);
          nextLineNumber = newSnapshot.GetLineFromPosition(end).LineNumber;
        }
        _buffer.Properties[bufferTokenTaggerKey] = new ScanResult(null, newSnapshot, newRegions, null);
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
