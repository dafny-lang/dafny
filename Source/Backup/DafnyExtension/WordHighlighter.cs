using System;
using System.Collections.Generic;
using System.ComponentModel.Composition;
using System.Linq;
using System.Windows.Media;
using Microsoft.VisualStudio.Text;
using Microsoft.VisualStudio.Text.Classification;
using Microsoft.VisualStudio.Text.Editor;
using Microsoft.VisualStudio.Text.Operations;
using Microsoft.VisualStudio.Text.Tagging;
using Microsoft.VisualStudio.Utilities;


namespace DafnyLanguage
{

#if LATER_MAYBE

  #region (the current annoying) word highligher

  internal class HighlightWordTagger : ITagger<HighlightWordTag>
  {
    ITextView View { get; set; }
    ITextBuffer SourceBuffer { get; set; }
    ITextSearchService TextSearchService { get; set; }
    ITextStructureNavigator TextStructureNavigator { get; set; }
    NormalizedSnapshotSpanCollection WordSpans { get; set; }
    SnapshotSpan? CurrentWord { get; set; }
    SnapshotPoint RequestedPoint { get; set; }
    object updateLock = new object();

    public HighlightWordTagger(ITextView view, ITextBuffer sourceBuffer, ITextSearchService textSearchService,
    ITextStructureNavigator textStructureNavigator) {
      this.View = view;
      this.SourceBuffer = sourceBuffer;
      this.TextSearchService = textSearchService;
      this.TextStructureNavigator = textStructureNavigator;
      this.WordSpans = new NormalizedSnapshotSpanCollection();
      this.CurrentWord = null;
      this.View.Caret.PositionChanged += CaretPositionChanged;
      this.View.LayoutChanged += ViewLayoutChanged;
    }

    void ViewLayoutChanged(object sender, TextViewLayoutChangedEventArgs e) {
      // If a new snapshot wasn't generated, then skip this layout
      if (e.NewSnapshot != e.OldSnapshot) {
        UpdateAtCaretPosition(View.Caret.Position);
      }
    }

    void CaretPositionChanged(object sender, CaretPositionChangedEventArgs e) {
      UpdateAtCaretPosition(e.NewPosition);
    }

    public event EventHandler<SnapshotSpanEventArgs> TagsChanged;

    void UpdateAtCaretPosition(CaretPosition caretPosition) {
      SnapshotPoint? point = caretPosition.Point.GetPoint(SourceBuffer, caretPosition.Affinity);

      if (!point.HasValue)
        return;

      // If the new caret position is still within the current word (and on the same snapshot), we don't need to check it
      if (CurrentWord.HasValue
          && CurrentWord.Value.Snapshot == View.TextSnapshot
          && CurrentWord.Value.Start <= point.Value && point.Value <= CurrentWord.Value.End) {
        return;
      }

      RequestedPoint = point.Value;
      UpdateWordAdornments();
    }

    void UpdateWordAdornments() {
      SnapshotPoint currentRequest = RequestedPoint;
      List<SnapshotSpan> wordSpans = new List<SnapshotSpan>();
      //Find all words in the buffer like the one the caret is on
      TextExtent word = TextStructureNavigator.GetExtentOfWord(currentRequest);
      bool foundWord = true;
      //If we've selected something not worth highlighting, we might have missed a "word" by a little bit
      if (!WordExtentIsValid(currentRequest, word)) {
        //Before we retry, make sure it is worthwhile
        if (word.Span.Start != currentRequest
             || currentRequest == currentRequest.GetContainingLine().Start
             || char.IsWhiteSpace((currentRequest - 1).GetChar())) {
          foundWord = false;
        } else {
          // Try again, one character previous.
          //If the caret is at the end of a word, pick up the word.
          word = TextStructureNavigator.GetExtentOfWord(currentRequest - 1);

          //If the word still isn't valid, we're done
          if (!WordExtentIsValid(currentRequest, word))
            foundWord = false;
        }
      }

      if (!foundWord) {
        //If we couldn't find a word, clear out the existing markers
        SynchronousUpdate(currentRequest, new NormalizedSnapshotSpanCollection(), null);
        return;
      }

      SnapshotSpan currentWord = word.Span;
      //If this is the current word, and the caret moved within a word, we're done.
      if (CurrentWord.HasValue && currentWord == CurrentWord)
        return;

      //Find the new spans
      FindData findData = new FindData(currentWord.GetText(), currentWord.Snapshot);
      findData.FindOptions = FindOptions.WholeWord | FindOptions.MatchCase;

      wordSpans.AddRange(TextSearchService.FindAll(findData));

      //If another change hasn't happened, do a real update
      if (currentRequest == RequestedPoint)
        SynchronousUpdate(currentRequest, new NormalizedSnapshotSpanCollection(wordSpans), currentWord);
    }

    static bool WordExtentIsValid(SnapshotPoint currentRequest, TextExtent word) {
      return word.IsSignificant
          && currentRequest.Snapshot.GetText(word.Span).Any(c => char.IsLetter(c));
    }

    void SynchronousUpdate(SnapshotPoint currentRequest, NormalizedSnapshotSpanCollection newSpans, SnapshotSpan? newCurrentWord) {
      lock (updateLock) {
        if (currentRequest != RequestedPoint)
          return;

        WordSpans = newSpans;
        CurrentWord = newCurrentWord;

        var chngd = TagsChanged;
        if (chngd != null)
          chngd(this, new SnapshotSpanEventArgs(new SnapshotSpan(SourceBuffer.CurrentSnapshot, 0, SourceBuffer.CurrentSnapshot.Length)));
      }
    }

    public IEnumerable<ITagSpan<HighlightWordTag>> GetTags(NormalizedSnapshotSpanCollection spans) {
      if (CurrentWord == null)
        yield break;

      // Hold on to a "snapshot" of the word spans and current word, so that we maintain the same
      // collection throughout
      SnapshotSpan currentWord = CurrentWord.Value;
      NormalizedSnapshotSpanCollection wordSpans = WordSpans;

      if (spans.Count == 0 || WordSpans.Count == 0)
        yield break;

      // If the requested snapshot isn't the same as the one our words are on, translate our spans to the expected snapshot
      if (spans[0].Snapshot != wordSpans[0].Snapshot) {
        wordSpans = new NormalizedSnapshotSpanCollection(
            wordSpans.Select(span => span.TranslateTo(spans[0].Snapshot, SpanTrackingMode.EdgeExclusive)));

        currentWord = currentWord.TranslateTo(spans[0].Snapshot, SpanTrackingMode.EdgeExclusive);
      }

      // First, yield back the word the cursor is under (if it overlaps)
      // Note that we'll yield back the same word again in the wordspans collection;
      // the duplication here is expected.
      if (spans.OverlapsWith(new NormalizedSnapshotSpanCollection(currentWord)))
        yield return new TagSpan<HighlightWordTag>(currentWord, new HighlightWordTag());

      // Second, yield all the other words in the file
      foreach (SnapshotSpan span in NormalizedSnapshotSpanCollection.Overlap(spans, wordSpans)) {
        yield return new TagSpan<HighlightWordTag>(span, new HighlightWordTag());
      }
    }
  }

  internal class HighlightWordTag : TextMarkerTag
  {
    public HighlightWordTag() : base("MarkerFormatDefinition/HighlightWordFormatDefinition") { }
  }

  [Export(typeof(EditorFormatDefinition))]
  [Name("MarkerFormatDefinition/HighlightWordFormatDefinition")]
  [UserVisible(true)]
  internal class HighlightWordFormatDefinition : MarkerFormatDefinition
  {
    public HighlightWordFormatDefinition() {
      this.BackgroundColor = Colors.LightBlue;
      this.ForegroundColor = Colors.DarkBlue;
      this.DisplayName = "Highlight Word";
      this.ZOrder = 5;
    }
  }

  [Export(typeof(IViewTaggerProvider))]
  [ContentType("text")]
  [TagType(typeof(TextMarkerTag))]
  internal class HighlightWordTaggerProvider : IViewTaggerProvider
  {
    [Import]
    internal ITextSearchService TextSearchService { get; set; }

    [Import]
    internal ITextStructureNavigatorSelectorService TextStructureNavigatorSelector { get; set; }

    public ITagger<T> CreateTagger<T>(ITextView textView, ITextBuffer buffer) where T : ITag {
      //provide highlighting only on the top buffer
      if (textView.TextBuffer != buffer)
        return null;

      ITextStructureNavigator textStructureNavigator =
          TextStructureNavigatorSelector.GetTextStructureNavigator(buffer);

      return new HighlightWordTagger(textView, buffer, TextSearchService, textStructureNavigator) as ITagger<T>;
    }
  }

  #endregion

#endif

}
