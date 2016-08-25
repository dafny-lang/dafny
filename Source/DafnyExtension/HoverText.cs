using System.Collections.Generic;
using System.ComponentModel.Composition;
using System.Linq;
using Microsoft.VisualStudio.Language.Intellisense;
using Microsoft.VisualStudio.Text;
using Microsoft.VisualStudio.Text.Editor;
using Microsoft.VisualStudio.Text.Tagging;
using Microsoft.VisualStudio.Utilities;


namespace DafnyLanguage
{

  #region Source Provider

  [Export(typeof(IQuickInfoSourceProvider))]
  [ContentType("dafny")]
  [Name("Dafny QuickInfo")]
  class DafnyQuickInfoSourceProvider : IQuickInfoSourceProvider
  {
    [Import]
    IBufferTagAggregatorFactoryService aggService = null;

    public IQuickInfoSource TryCreateQuickInfoSource(ITextBuffer textBuffer) {
      return new DafnyQuickInfoSource(textBuffer, aggService.CreateTagAggregator<DafnyTokenTag>(textBuffer));
    }
  }

  class DafnyQuickInfoSource : IQuickInfoSource
  {
    private ITagAggregator<DafnyTokenTag> _aggregator;
    private ITextBuffer _buffer;

    public DafnyQuickInfoSource(ITextBuffer buffer, ITagAggregator<DafnyTokenTag> aggregator)
    {
      _aggregator = aggregator;
      _buffer = buffer;
    }

    public void AugmentQuickInfoSession(IQuickInfoSession session, IList<object> quickInfoContent, out ITrackingSpan applicableToSpan)
    {
      applicableToSpan = null;

      var triggerPoint = (SnapshotPoint)session.GetTriggerPoint(_buffer.CurrentSnapshot);
      if (triggerPoint == null)
        return;

      foreach (IMappingTagSpan<DafnyTokenTag> curTag in _aggregator.GetTags(new SnapshotSpan(triggerPoint, triggerPoint)))
      {
        var s = curTag.Tag.HoverText;
        if (s != null)
        {
          var tagSpan = curTag.Span.GetSpans(_buffer).First();
          applicableToSpan = _buffer.CurrentSnapshot.CreateTrackingSpan(tagSpan, SpanTrackingMode.EdgeExclusive);
          quickInfoContent.Add(s);
        }
      }
    }
    public void Dispose()
    {
    }
  }

  #endregion


  #region Controller Provider

  [Export(typeof(IIntellisenseControllerProvider))]
  [Name("Dafny QuickInfo controller")]
  [ContentType("dafny")]
  class DafnyQuickInfoControllerProvider : IIntellisenseControllerProvider
  {
    [Import]
    internal IQuickInfoBroker QuickInfoBroker { get; set; }

    public IIntellisenseController TryCreateIntellisenseController(ITextView textView, IList<ITextBuffer> subjectBuffers) {
      return new DafnyQuickInfoController(textView, subjectBuffers, this);
    }
  }

  #endregion


  #region Controller

  class DafnyQuickInfoController : IIntellisenseController
  {
    private ITextView _textView;
    private IList<ITextBuffer> _subjectBuffers;
    private DafnyQuickInfoControllerProvider _componentContext;

    private IQuickInfoSession _session;

    internal DafnyQuickInfoController(ITextView textView, IList<ITextBuffer> subjectBuffers, DafnyQuickInfoControllerProvider componentContext) {
      _textView = textView;
      _subjectBuffers = subjectBuffers;
      _componentContext = componentContext;

      _textView.MouseHover += this.OnTextViewMouseHover;
    }

    public void ConnectSubjectBuffer(ITextBuffer subjectBuffer) {
    }

    public void DisconnectSubjectBuffer(ITextBuffer subjectBuffer) {
    }

    public void Detach(ITextView textView) {
      if (_textView == textView) {
        _textView.MouseHover -= OnTextViewMouseHover;
        _textView = null;
      }
    }

    void OnTextViewMouseHover(object sender, MouseHoverEventArgs e) {
      SnapshotPoint? point = GetMousePosition(new SnapshotPoint(_textView.TextSnapshot, e.Position));

      if (point != null) {
        ITrackingPoint triggerPoint = point.Value.Snapshot.CreateTrackingPoint(point.Value.Position, PointTrackingMode.Positive);

        // Find the broker for this buffer
        if (!_componentContext.QuickInfoBroker.IsQuickInfoActive(_textView)) {
          _session = _componentContext.QuickInfoBroker.CreateQuickInfoSession(_textView, triggerPoint, true);
          _session.Start();
        }
      }
    }

    SnapshotPoint? GetMousePosition(SnapshotPoint topPosition) {
      return _textView.BufferGraph.MapDownToFirstMatch(
        topPosition,
        PointTrackingMode.Positive,
        snapshot => _subjectBuffers.Contains(snapshot.TextBuffer),
        PositionAffinity.Predecessor);
    }
  }

  #endregion

}
