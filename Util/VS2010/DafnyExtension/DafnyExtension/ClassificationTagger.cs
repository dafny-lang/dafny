using System;
using System.Collections.Generic;
using System.ComponentModel.Composition;
using System.Windows.Media;
using Microsoft.VisualStudio.Text;
using Microsoft.VisualStudio.Text.Classification;
using Microsoft.VisualStudio.Text.Editor;
using Microsoft.VisualStudio.Text.Tagging;
using Microsoft.VisualStudio.Utilities;


namespace DafnyLanguage
{
  [Export(typeof(ITaggerProvider))]
  [ContentType("dafny")]
  [TagType(typeof(ClassificationTag))]
  internal sealed class DafnyClassifierProvider : ITaggerProvider
  {
    [Import]
    internal IBufferTagAggregatorFactoryService AggregatorFactory = null;

    [Import]
    internal IClassificationTypeRegistryService ClassificationTypeRegistry = null;

    [Import]
    internal Microsoft.VisualStudio.Language.StandardClassification.IStandardClassificationService Standards = null;

    public ITagger<T> CreateTagger<T>(ITextBuffer buffer) where T : ITag {
      ITagAggregator<DafnyTokenTag> tagAggregator = AggregatorFactory.CreateTagAggregator<DafnyTokenTag>(buffer);
      return new DafnyClassifier(buffer, tagAggregator, ClassificationTypeRegistry, Standards) as ITagger<T>;
    }
  }

  internal sealed class DafnyClassifier : ITagger<ClassificationTag>
  {
    ITextBuffer _buffer;
    ITagAggregator<DafnyTokenTag> _aggregator;
    IDictionary<DafnyTokenKinds, IClassificationType> _typeMap;

    internal DafnyClassifier(ITextBuffer buffer,
                             ITagAggregator<DafnyTokenTag> tagAggregator,
                             IClassificationTypeRegistryService typeService, Microsoft.VisualStudio.Language.StandardClassification.IStandardClassificationService standards) {
      _buffer = buffer;
      _aggregator = tagAggregator;
      _aggregator.TagsChanged += new EventHandler<TagsChangedEventArgs>(_aggregator_TagsChanged);
      // use built-in classification types:
      _typeMap = new Dictionary<DafnyTokenKinds, IClassificationType>();
      _typeMap[DafnyTokenKinds.Keyword] = standards.Keyword;
      _typeMap[DafnyTokenKinds.Number] = standards.NumberLiteral;
      _typeMap[DafnyTokenKinds.String] = standards.StringLiteral;
      _typeMap[DafnyTokenKinds.Comment] = standards.Comment;
      _typeMap[DafnyTokenKinds.VariableIdentifier] = standards.Identifier;
      _typeMap[DafnyTokenKinds.TypeIdentifier] = typeService.GetClassificationType("Dafny user type");
    }

    public event EventHandler<SnapshotSpanEventArgs> TagsChanged;

    public IEnumerable<ITagSpan<ClassificationTag>> GetTags(NormalizedSnapshotSpanCollection spans) {
      if (spans.Count == 0) yield break;
      var snapshot = spans[0].Snapshot;
      foreach (var tagSpan in this._aggregator.GetTags(spans)) {
        IClassificationType t = _typeMap[tagSpan.Tag.Kind];
        foreach (SnapshotSpan s in tagSpan.Span.GetSpans(snapshot)) {
          yield return new TagSpan<ClassificationTag>(s, new ClassificationTag(t));
        }
      }
    }

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

  /// <summary>
  /// Defines an editor format for user-defined type.
  /// </summary>
  [Export(typeof(EditorFormatDefinition))]
  [ClassificationType(ClassificationTypeNames = "Dafny user type")]
  [Name("Dafny user type")]
  [UserVisible(true)]
  //set the priority to be after the default classifiers
  [Order(Before = Priority.Default)]
  internal sealed class DafnyTypeFormat : ClassificationFormatDefinition
  {
    public DafnyTypeFormat() {
      this.DisplayName = "Dafny user type"; //human readable version of the name
      this.ForegroundColor = Colors.Coral;
    }
  }

  internal static class ClassificationDefinition
  {
    /// <summary>
    /// Defines the "ordinary" classification type.
    /// </summary>
    [Export(typeof(ClassificationTypeDefinition))]
    [Name("Dafny user type")]
    internal static ClassificationTypeDefinition UserType = null;
  }
}
