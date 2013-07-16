//***************************************************************************
// Copyright © 2010 Microsoft Corporation.  All Rights Reserved.
// This code released under the terms of the
// Microsoft Public License (MS-PL, http://opensource.org/licenses/ms-pl.html.)
//***************************************************************************


using System;
using System.Collections.Generic;
using System.ComponentModel.Composition;
using System.Diagnostics.Contracts;
using System.Windows;
using System.Windows.Input;
using System.Windows.Media;
using System.Windows.Shapes;
using Microsoft.VisualStudio.Text;
using Microsoft.VisualStudio.Text.Editor;
using Microsoft.VisualStudio.Text.Tagging;
using Microsoft.VisualStudio.Utilities;


namespace DafnyLanguage
{

  #region Provider

  [Export(typeof(IViewTaggerProvider))]
  [ContentType("dafny")]
  [Name("ErrorModelTagger")]
  [Order(After = "ErrorTagger")]
  [TextViewRole(PredefinedTextViewRoles.Document)]
  [TagType(typeof(IntraTextAdornmentTag))]
  internal sealed class ErrorModelTaggerProvider : IViewTaggerProvider
  {
    [Import]
    internal IBufferTagAggregatorFactoryService BufferTagAggregatorFactoryService = null;

    public ITagger<T> CreateTagger<T>(ITextView textView, ITextBuffer buffer) where T : ITag
    {
      if (textView == null)
        throw new ArgumentNullException("textView");

      if (buffer == null)
        throw new ArgumentNullException("buffer");

      if (buffer != textView.TextBuffer)
        return null;

      return ErrorModelTagger.GetTagger(
                (IWpfTextView)textView,
                new Lazy<ITagAggregator<IDafnyResolverTag>>(
                    () => BufferTagAggregatorFactoryService.CreateTagAggregator<IDafnyResolverTag>(textView.TextBuffer)))
                as ITagger<T>;
    }
  }

  #endregion


  #region Tagger

  internal sealed class ErrorModelTagger : IntraTextAdornmentTagger<IDafnyResolverTag, Ellipse>, IDisposable
  {
    IWpfTextView _view;
    ITagAggregator<IDafnyResolverTag> _aggregator;

    internal static ITagger<IntraTextAdornmentTag> GetTagger(IWpfTextView view, Lazy<ITagAggregator<IDafnyResolverTag>> aggregator)
    {
      return view.Properties.GetOrCreateSingletonProperty<ErrorModelTagger>(
            () => new ErrorModelTagger(view, aggregator.Value));
    }

    private ErrorModelTagger(IWpfTextView view, ITagAggregator<IDafnyResolverTag> aggregator)
      : base(view)
    {
      _view = view;
      _aggregator = aggregator;
      _aggregator.TagsChanged += new EventHandler<TagsChangedEventArgs>(_aggregator_TagsChanged);
    }

    public void Dispose()
    {
      this._aggregator.Dispose();

      base.view.Properties.RemoveProperty(typeof(ErrorModelTagger));
    }

    // To produce adornments that don't obscure the text, the adornment tags
    // should have zero length spans. Overriding this method allows control
    // over the tag spans.
    protected override IEnumerable<Tuple<SnapshotSpan, PositionAffinity?, IDafnyResolverTag>> GetAdornmentData(NormalizedSnapshotSpanCollection spans)
    {
      if (spans.Count == 0)
        yield break;

      ITextSnapshot snapshot = spans[0].Snapshot;

      var tags = this._aggregator.GetTags(spans);

      foreach (IMappingTagSpan<IDafnyResolverTag> tag in tags)
      {
        var ertag = tag.Tag as DafnyErrorResolverTag;
        if (ertag != null && ertag.Error.Model != null)
        {
          NormalizedSnapshotSpanCollection normSpans = tag.Span.GetSpans(snapshot);

          // Ignore data tags that are split by projection.
          // This is theoretically possible but unlikely in current scenarios.
          if (normSpans.Count != 1)
            continue;

          yield return Tuple.Create(new SnapshotSpan(normSpans[0].Start, 0), (PositionAffinity?)PositionAffinity.Successor, tag.Tag);
        }
      }
    }

    protected override Ellipse CreateAdornment(IDafnyResolverTag data, SnapshotSpan span)
    {
      var ertag = data as DafnyErrorResolverTag;
      Contract.Assert(ertag != null);

      var result = new Ellipse
        {
          Fill = Brushes.Red,
          Height = 12.0, Width = 12.0,
          ToolTip = "select error",
          StrokeThickness = 3.0,
          Stroke = Brushes.Red,
          Cursor = Cursors.Arrow,
          
        };
      result.MouseDown += new MouseButtonEventHandler((s, e) =>
      {
        if (ertag.Error.SelectedError == ertag.Error)
        {
          // unselect it
          ertag.Error.SelectedError = null;
          result.Stroke = Brushes.Red;
          result.ToolTip = "select error";
        }
        else
        {
          // unselect the old one
          if (ertag.Error.SelectedError != null)
          {
            ertag.Error.SelectedError.Adornment.Stroke = Brushes.Red;
            ertag.Error.SelectedError.Adornment.ToolTip = "select error";
            ertag.Error.SelectedError = null;
          }

          // select the new one
          ertag.Error.SelectedError = ertag.Error;
          ertag.Error.Adornment = result;          
          ertag.Error.Adornment.Stroke = Brushes.Black;
          ertag.Error.Adornment.ToolTip = "unselect error";
        }
      });
      return result;
    }

    protected override bool UpdateAdornment(Ellipse adornment, IDafnyResolverTag data)
    {
      return false;
    }

    void _aggregator_TagsChanged(object sender, TagsChangedEventArgs e)
    {      
      NormalizedSnapshotSpanCollection spans = e.Span.GetSpans(_view.TextBuffer.CurrentSnapshot);
      if (spans.Count > 0)
      {
        var span = new SnapshotSpan(spans[0].Start, spans[spans.Count - 1].End);
        InvalidateSpans(new List<SnapshotSpan> { span });
      }
    }
  }

  #endregion

}
