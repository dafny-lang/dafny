using System;
using System.Collections.Generic;
using System.ComponentModel.Composition;
using Microsoft.VisualStudio.Text;
using Microsoft.VisualStudio.Text.Tagging;
using Microsoft.VisualStudio.Utilities;


namespace DafnyLanguage
{

  #region Provider

  [Export(typeof(ITaggerProvider))]
  [Name("ErrorTagger")]
  [ContentType("dafny")]
  [TagType(typeof(IErrorTag))]
  internal sealed class ErrorTaggerProvider : ITaggerProvider
  {
    [Import]
    internal IBufferTagAggregatorFactoryService AggregatorFactory = null;

    public ITagger<T> CreateTagger<T>(ITextBuffer buffer) where T : ITag {
      ITagAggregator<IDafnyResolverTag> tagAggregator = AggregatorFactory.CreateTagAggregator<IDafnyResolverTag>(buffer);
      // create a single tagger for each buffer.
      Func<ITagger<T>> sc = delegate() { return new ErrorTagger(buffer, tagAggregator) as ITagger<T>; };
      return buffer.Properties.GetOrCreateSingletonProperty<ITagger<T>>(sc);
    }
  }

  #endregion


  #region Tagger

  /// <summary>
  /// Translate PkgDefTokenTags into ErrorTags and Error List items
  /// </summary>
  internal sealed class ErrorTagger : ITagger<IErrorTag>
  {
    ITextBuffer _buffer;
    ITagAggregator<IDafnyResolverTag> _aggregator;

    internal ErrorTagger(ITextBuffer buffer, ITagAggregator<IDafnyResolverTag> tagAggregator) {
      _buffer = buffer;
      _aggregator = tagAggregator;
      _aggregator.TagsChanged += new EventHandler<TagsChangedEventArgs>(_aggregator_TagsChanged);
    }

    /// <summary>
    /// Find the Error tokens in the set of all tokens and create an ErrorTag for each
    /// </summary>
    public IEnumerable<ITagSpan<IErrorTag>> GetTags(NormalizedSnapshotSpanCollection spans) {
      if (spans.Count == 0) yield break;
      var snapshot = spans[0].Snapshot;
      foreach (var tagSpan in _aggregator.GetTags(spans)) {
        var et = tagSpan.Tag as IErrorTag;
        if (et != null) {
          foreach (SnapshotSpan s in tagSpan.Span.GetSpans(snapshot)) {
            yield return new TagSpan<IErrorTag>(s, et);
          }
        }
      }
    }

    // the Classifier tagger is translating buffer change events into TagsChanged events, so we don't have to
    public event EventHandler<SnapshotSpanEventArgs> TagsChanged;

    void _aggregator_TagsChanged(object sender, TagsChangedEventArgs e) {
      var chng = TagsChanged;
      if (chng != null) {
        NormalizedSnapshotSpanCollection spans = e.Span.GetSpans(_buffer.CurrentSnapshot);
        if (spans.Count > 0) {
          SnapshotSpan span = new SnapshotSpan(spans[0].Start, spans[spans.Count - 1].End);
          chng(this, new SnapshotSpanEventArgs(span));
        }
      }
    }
  }

  #endregion

}
