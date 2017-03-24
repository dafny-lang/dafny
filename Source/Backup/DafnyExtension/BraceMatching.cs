using System;
using System.Collections.Generic;
using System.ComponentModel.Composition;
using Microsoft.VisualStudio.Text;
using Microsoft.VisualStudio.Text.Editor;
using Microsoft.VisualStudio.Text.Tagging;
using Microsoft.VisualStudio.Utilities;


namespace DafnyLanguage
{

  #region Provider

  [Export(typeof(IViewTaggerProvider))]
  [ContentType("dafny")]
  [TagType(typeof(TextMarkerTag))]
  internal class BraceMatchingTaggerProvider : IViewTaggerProvider
  {
    [Import]
    internal IBufferTagAggregatorFactoryService AggregatorFactory = null;

    public ITagger<T> CreateTagger<T>(ITextView textView, ITextBuffer buffer) where T : ITag {
      if (textView == null)
        return null;

      //provide highlighting only on the top-level buffer
      if (textView.TextBuffer != buffer)
        return null;

      ITagAggregator<DafnyTokenTag> tagAggregator = AggregatorFactory.CreateTagAggregator<DafnyTokenTag>(buffer);
      return new BraceMatchingTagger(textView, buffer, tagAggregator) as ITagger<T>;
    }
  }

  #endregion


  #region Tagger

  internal abstract class TokenBasedTagger
  {
    ITagAggregator<DafnyTokenTag> _aggregator;

    internal TokenBasedTagger(ITagAggregator<DafnyTokenTag> tagAggregator) {
      _aggregator = tagAggregator;
    }

    public bool InsideComment(SnapshotPoint pt) {
      SnapshotSpan span = new SnapshotSpan(pt, 1);
      foreach (var tagSpan in this._aggregator.GetTags(span)) {
        switch (tagSpan.Tag.Kind) {
          case DafnyTokenKind.Comment:
          case DafnyTokenKind.String:
            foreach (var s in tagSpan.Span.GetSpans(pt.Snapshot)) {
              if (s.Contains(span))
                return true;
            }
            break;
          default:
            break;
        }
      }
      return false;
    }
  }


  internal class BraceMatchingTagger : TokenBasedTagger, ITagger<TextMarkerTag>
  {
    ITextView View { get; set; }
    ITextBuffer SourceBuffer { get; set; }
    SnapshotPoint? CurrentChar { get; set; }
    private char[] openBraces;
    private char[] closeBraces;

    static TextMarkerTag Blue = new TextMarkerTag("blue");

    internal BraceMatchingTagger(ITextView view, ITextBuffer sourceBuffer, ITagAggregator<DafnyTokenTag> tagAggregator)
      : base(tagAggregator)
    {
      //here the keys are the open braces, and the values are the close braces
      openBraces =  new char[] { '(', '{', '[' };
      closeBraces = new char[] { ')', '}', ']' };
      this.View = view;
      this.SourceBuffer = sourceBuffer;
      this.CurrentChar = null;

      this.View.Caret.PositionChanged += CaretPositionChanged;
      this.View.LayoutChanged += ViewLayoutChanged;
    }

    public event EventHandler<SnapshotSpanEventArgs> TagsChanged;

    void ViewLayoutChanged(object sender, TextViewLayoutChangedEventArgs e) {
      if (e.NewSnapshot != e.OldSnapshot) //make sure that there has really been a change
      {
        UpdateAtCaretPosition(View.Caret.Position);
      }
    }

    void CaretPositionChanged(object sender, CaretPositionChangedEventArgs e) {
      UpdateAtCaretPosition(e.NewPosition);
    }

    void UpdateAtCaretPosition(CaretPosition caretPosition) {
      CurrentChar = caretPosition.Point.GetPoint(SourceBuffer, caretPosition.Affinity);

      if (!CurrentChar.HasValue)
        return;

      var chngd = TagsChanged;
      if (chngd != null)
        chngd(this, new SnapshotSpanEventArgs(new SnapshotSpan(SourceBuffer.CurrentSnapshot, 0, SourceBuffer.CurrentSnapshot.Length)));
    }

    public IEnumerable<ITagSpan<TextMarkerTag>> GetTags(NormalizedSnapshotSpanCollection spans) {
      if (spans.Count == 0)   //there is no content in the buffer
        yield break;

      //don't do anything if the current SnapshotPoint is not initialized
      if (!CurrentChar.HasValue)
        yield break;

      //hold on to a snapshot of the current character
      SnapshotPoint currentChar = CurrentChar.Value;

      //if the requested snapshot isn't the same as the one the brace is on, translate our spans to the expected snapshot
      if (spans[0].Snapshot != currentChar.Snapshot) {
        currentChar = currentChar.TranslateTo(spans[0].Snapshot, PointTrackingMode.Positive);
      }

      if (currentChar.Position < spans[0].Snapshot.Length) {
        // Check if the current character is an open brace
        char ch = currentChar.GetChar();
        char closeCh;
        if (MatchBrace(currentChar, ch, true, out closeCh)) {
          SnapshotSpan pairSpan;
          if (FindMatchingCloseChar(currentChar, ch, closeCh, View.TextViewLines.Count, out pairSpan)) {
            yield return new TagSpan<TextMarkerTag>(new SnapshotSpan(currentChar, 1), Blue);
            yield return new TagSpan<TextMarkerTag>(pairSpan, Blue);
          }
        }
      }

      if (0 < currentChar.Position) {
        // Check if the previous character is a close brace (note, caret may be between a close brace and an open brace, in which case we'll tag two pairs)
        SnapshotPoint prevChar = currentChar - 1;
        char ch = prevChar.GetChar();
        char openCh;
        if (MatchBrace(prevChar, ch, false, out openCh)) {
          SnapshotSpan pairSpan;
          if (FindMatchingOpenChar(prevChar, openCh, ch, View.TextViewLines.Count, out pairSpan)) {
            yield return new TagSpan<TextMarkerTag>(new SnapshotSpan(prevChar, 1), Blue);
            yield return new TagSpan<TextMarkerTag>(pairSpan, Blue);
          }
        }
      }
    }

    private bool MatchBrace(SnapshotPoint pt, char query, bool sourceIsOpen, out char match) {
      if (!InsideComment(pt)) {
        char[] source = sourceIsOpen ? openBraces : closeBraces;
        int i = 0;
        foreach (char ch in source) {
          if (ch == query) {
            char[] dest = sourceIsOpen ? closeBraces : openBraces;
            match = dest[i];
            return true;
          }
          i++;
        }
      }
      match = query;  // satisfy compiler
      return false;
    }

    private bool FindMatchingCloseChar(SnapshotPoint startPoint, char open, char close, int linesViewed, out SnapshotSpan pairSpan) {
      ITextSnapshotLine line = startPoint.GetContainingLine();
      int lineNumber = line.LineNumber;
      int offset = startPoint.Position - line.Start.Position + 1;

      int lineNumberLimit = Math.Min(startPoint.Snapshot.LineCount, lineNumber + linesViewed);

      int openCount = 0;
      while (true) {
        string lineText = line.GetText();

        //walk the entire line
        for (; offset < line.Length; offset++) {
          char currentChar = lineText[offset];
          if (currentChar == open || currentChar == close) {
            if (!InsideComment(new SnapshotPoint(line.Snapshot, line.Start.Position + offset))) {
              if (currentChar == open) {
                openCount++;
              } else if (0 < openCount) {
                openCount--;
              } else {
                //found the matching close
                pairSpan = new SnapshotSpan(startPoint.Snapshot, line.Start + offset, 1);
                return true;
              }
            }
          }
        }

        //move on to the next line
        lineNumber++;
        if (lineNumberLimit <= lineNumber)
          break;

        line = line.Snapshot.GetLineFromLineNumber(lineNumber);
        offset = 0;
      }

      pairSpan = new SnapshotSpan(startPoint, startPoint);  // satisfy the compiler
      return false;
    }

    private bool FindMatchingOpenChar(SnapshotPoint startPoint, char open, char close, int linesViewed, out SnapshotSpan pairSpan) {
      ITextSnapshotLine line = startPoint.GetContainingLine();
      int lineNumber = line.LineNumber;
      int offset = startPoint.Position - line.Start.Position - 1; //move the offset to the character before this one

      int lineNumberLimit = Math.Max(0, lineNumber - linesViewed);

      int closeCount = 0;
      while (true) {
        string lineText = line.GetText();

        //walk the entire line
        for (; 0 <= offset; offset--) {
          char currentChar = lineText[offset];
          if (currentChar == open || currentChar == close) {
            if (!InsideComment(new SnapshotPoint(line.Snapshot, line.Start.Position + offset))) {
              if (currentChar == close) {
                closeCount++;
              } else if (0 < closeCount) {
                closeCount--;
              } else {
                // We've found the open character
                pairSpan = new SnapshotSpan(line.Start + offset, 1); //we just want the character itself
                return true;
              }
            }
          }
        }

        // Move to the previous line
        lineNumber--;
        if (lineNumber < lineNumberLimit)
          break;

        line = line.Snapshot.GetLineFromLineNumber(lineNumber);
        offset = line.Length - 1;
      }

      pairSpan = new SnapshotSpan(startPoint, startPoint);  // satisfy the compiler
      return false;
    }
  }

  #endregion

}
