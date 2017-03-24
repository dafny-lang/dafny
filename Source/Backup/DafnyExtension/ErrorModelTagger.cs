using System;
using System.Collections.Generic;
using System.ComponentModel.Composition;
using System.Linq;
using System.Windows;
using System.Windows.Controls;
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
  [Order(After = "ProgressTagger")]
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

  internal sealed class ErrorModelTagger : ITagger<IntraTextAdornmentTag>, IDisposable
  {
    IWpfTextView _view;
    ITagAggregator<IDafnyResolverTag> _aggregator;

    internal static ITagger<IntraTextAdornmentTag> GetTagger(IWpfTextView view, Lazy<ITagAggregator<IDafnyResolverTag>> aggregator)
    {
      return view.Properties.GetOrCreateSingletonProperty<ErrorModelTagger>(
            () => new ErrorModelTagger(view, aggregator.Value));
    }

    private ErrorModelTagger(IWpfTextView view, ITagAggregator<IDafnyResolverTag> aggregator)
    {
      _view = view;
      _aggregator = aggregator;
      _aggregator.TagsChanged += new EventHandler<TagsChangedEventArgs>(_aggregator_TagsChanged);
    }

    public void Dispose()
    {
      _aggregator.Dispose();
      _view.Properties.RemoveProperty(typeof(ErrorModelTagger));
    }

    public IEnumerable<ITagSpan<IntraTextAdornmentTag>> GetTags(NormalizedSnapshotSpanCollection spans)
    {
      if (spans.Count == 0) yield break;
      var snapshot = spans[0].Snapshot;

      var adornmentsPerSnapshot = new Dictionary<SnapshotSpan, List<Ellipse>>();
      foreach (var tag in _aggregator.GetTags(spans))
      {
        var ertag = tag.Tag as DafnyErrorResolverTag;
        if (ertag != null && ertag.Error.ModelText != null)
        {
          NormalizedSnapshotSpanCollection normSpans = tag.Span.GetSpans(snapshot);

          if (normSpans.Count != 1)
            continue;

          var adornment = _view.VisualElement.Dispatcher.Invoke(() => CreateErrorAdornment(ertag));
          var span = new SnapshotSpan(normSpans[0].Start, 0);
          List<Ellipse> adornments;
          if (adornmentsPerSnapshot.TryGetValue(span, out adornments))
          {
            adornments.Add(adornment);
          }
          else
          {
            adornmentsPerSnapshot.Add(span, new List<Ellipse> { adornment });
          }
        }

        var esrtag = tag.Tag as DafnyErrorStateResolverTag;
        if (esrtag != null)
        {
          var adornment = _view.VisualElement.Dispatcher.Invoke(() => CreateErrorStateAdornment(esrtag));
          var span = esrtag.Span.GetSpan(snapshot);
          List<Ellipse> adornments;
          if (adornmentsPerSnapshot.TryGetValue(span, out adornments))
          {
            adornments.Add(adornment);
          }
          else
          {
            adornmentsPerSnapshot.Add(span, new List<Ellipse> { adornment });
          }
        }
      }

      foreach (var adornments in adornmentsPerSnapshot)
      {
        var panel = _view.VisualElement.Dispatcher.Invoke(() =>
        {
          var maxConcurrentAdornments = adornments.Value.Where(a => a.Fill == Brushes.Crimson).Count()    // number of error adornments
                                        + (adornments.Value.Any(a => a.Fill != Brushes.Crimson) ? 1 : 0); // number of error state adornments
          var p = new StackPanel
          {
            Orientation = Orientation.Horizontal,
            Width = 12.0 * maxConcurrentAdornments,
            Height = 12.0,
          };
          foreach (var adornment in adornments.Value)
          {
            p.Children.Add(adornment);
          }
          p.Measure(new Size(double.PositiveInfinity, double.PositiveInfinity));
          return p;
        });

        yield return new TagSpan<IntraTextAdornmentTag>(adornments.Key, new IntraTextAdornmentTag(panel, null, PositionAffinity.Successor));
      }
    }

    private static string ErrorStateToolTip(bool isSelected, string description)
    {
      return string.Format("{0}{1}", isSelected ? "unselect state" : "select state", !string.IsNullOrEmpty(description) ? " [" + description + "]" : "");
    }

    private Ellipse CreateErrorStateAdornment(DafnyErrorStateResolverTag esrtag)
    {
      var result = new Ellipse
      {
        Fill = Brushes.DodgerBlue,
        Height = 12.0,
        Width = 12.0,
        ToolTip = ErrorStateToolTip(false, esrtag.Description),
        StrokeThickness = 3.0,
        Stroke = Brushes.DodgerBlue,
        Cursor = Cursors.Arrow,
        Visibility = System.Windows.Visibility.Collapsed
      };

      esrtag.Error.StateChangeEvent += new DafnyError.StateChangeEventHandler((o) =>
      {
        _view.VisualElement.Dispatcher.Invoke(() =>
          {
            result.Visibility = esrtag.Error.IsSelected ? System.Windows.Visibility.Visible : System.Windows.Visibility.Collapsed;
            var isSelected = esrtag.Error.IsSelected && esrtag.Error.SelectedStateId == esrtag.Id;
            result.Stroke = isSelected ? Brushes.Black : Brushes.DodgerBlue;
            if (isSelected)
            {
              result.ToolTip = ErrorStateToolTip(isSelected, esrtag.Description);
              esrtag.Error.SelectedStateAdornment = result;
            }
          });
      });

      result.MouseDown += new MouseButtonEventHandler((s, e) =>
      {
        _view.VisualElement.Dispatcher.Invoke(() =>
          {
            if (!esrtag.Error.IsSelected) { return; }
            if (esrtag.Error.SelectedStateAdornment == result)
            {
              // unselect it
              esrtag.Error.SelectedStateAdornment = null;
              esrtag.Error.SelectedStateId = -1;
              result.Stroke = Brushes.DodgerBlue;
              result.ToolTip = result.ToolTip.ToString().Replace("unselect", "select");
            }
            else
            {
              // unselect the old one
              if (esrtag.Error.SelectedStateAdornment != null)
              {
                esrtag.Error.SelectedStateAdornment.Stroke = Brushes.DodgerBlue;
                esrtag.Error.SelectedStateAdornment.ToolTip = esrtag.Error.SelectedStateAdornment.ToolTip.ToString().Replace("unselect", "select");
                esrtag.Error.SelectedStateAdornment = null;
                esrtag.Error.SelectedStateId = -1;
              }

              // select the new one
              esrtag.Error.SelectedStateAdornment = result;
              esrtag.Error.SelectedStateAdornment.Stroke = Brushes.Black;
              esrtag.Error.SelectedStateAdornment.ToolTip = ErrorStateToolTip(true, esrtag.Description);
              esrtag.Error.SelectedStateId = esrtag.Id;
              if (!string.IsNullOrEmpty(esrtag.Error.ModelText))
              {
                DafnyClassifier.DafnyMenuPackage.ShowErrorModelInBVD(esrtag.Error.ModelText, esrtag.Id);
              }
            }
          });
      });
      return result;
    }

    private Ellipse CreateErrorAdornment(DafnyErrorResolverTag ertag)
    {
      var result = new Ellipse
      {
        Fill = Brushes.Crimson,
        Height = 12.0,
        Width = 12.0,
        ToolTip = "select error",
        StrokeThickness = 3.0,
        Stroke = Brushes.Crimson,
        Cursor = Cursors.Arrow,
      };

      result.Measure(new Size(double.PositiveInfinity, double.PositiveInfinity));
      result.MouseDown += new MouseButtonEventHandler((s, e) =>
      {
        _view.VisualElement.Dispatcher.Invoke(() =>
          {
            if (ertag.Error.IsSelected)
            {
              // unselect it
              var selErr = ertag.Error.SelectedError;
              selErr.SelectedStateId = -1;
              selErr.SelectedStateAdornment = null;
              ertag.Error.SelectedError = null;
              result.Stroke = Brushes.Crimson;
              result.ToolTip = "select error";
              selErr.Notify();
            }
            else
            {
              // unselect the old one
              if (ertag.Error.SelectedError != null)
              {
                var selErr = ertag.Error.SelectedError;
                selErr.SelectedStateId = -1;
                selErr.SelectedStateAdornment = null;
                selErr.Adornment.Stroke = Brushes.Crimson;
                selErr.Adornment.ToolTip = "select error";
                ertag.Error.SelectedError = null;
                selErr.Notify();
              }

              // select the new one
              ertag.Error.SelectedError = ertag.Error;
              ertag.Error.Adornment = result;
              ertag.Error.Adornment.Stroke = Brushes.Black;
              ertag.Error.Adornment.ToolTip = "unselect error";
              if (!string.IsNullOrEmpty(ertag.Error.ModelText))
              {
                // select the last error state
                ertag.Error.SelectedStateId = ertag.Error.Model.States.Count() - 1;
                ertag.Error.SelectedStateAdornment = null;
                DafnyClassifier.DafnyMenuPackage.ShowErrorModelInBVD(ertag.Error.ModelText, ertag.Error.SelectedStateId);
              }
              ertag.Error.SelectedError.Notify();
            }
          });
      });
      return result;
    }

    public event EventHandler<SnapshotSpanEventArgs> TagsChanged;

    void _aggregator_TagsChanged(object sender, TagsChangedEventArgs e)
    {
      var chng = TagsChanged;
      if (chng != null)
      {
        NormalizedSnapshotSpanCollection spans = e.Span.GetSpans(_view.TextBuffer.CurrentSnapshot);
        if (spans.Count > 0)
        {
          SnapshotSpan span = new SnapshotSpan(spans[0].Start, spans[spans.Count - 1].End);
          _view.VisualElement.Dispatcher.Invoke(() =>
            {
              chng(this, new SnapshotSpanEventArgs(span));
            });
        }
      }
    }
  }

  #endregion

}
