using System;
using System.Collections.Generic;
using System.ComponentModel.Composition;
using System.Windows.Media;
using Microsoft.VisualStudio.Text;
using Microsoft.VisualStudio.Text.Classification;
using Microsoft.VisualStudio.Text.Tagging;
using Microsoft.VisualStudio.Utilities;


namespace DafnyLanguage
{

  #region Provider

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

  #endregion

  #region Tagger

  internal sealed class DafnyClassifier : ITagger<ClassificationTag>
  {
    ITextBuffer _buffer;
    ITagAggregator<DafnyTokenTag> _aggregator;
    IDictionary<DafnyTokenKind, IClassificationType> _typeMap;

    internal static DafnyMenu.DafnyMenuPackage DafnyMenuPackage;

    internal DafnyClassifier(ITextBuffer buffer,
                             ITagAggregator<DafnyTokenTag> tagAggregator,
                             IClassificationTypeRegistryService typeService, Microsoft.VisualStudio.Language.StandardClassification.IStandardClassificationService standards) {
      _buffer = buffer;
      _aggregator = tagAggregator;
      _aggregator.TagsChanged += new EventHandler<TagsChangedEventArgs>(_aggregator_TagsChanged);

      // use built-in classification types:
      _typeMap = new Dictionary<DafnyTokenKind, IClassificationType>();
      _typeMap[DafnyTokenKind.Keyword] = standards.Keyword;
      _typeMap[DafnyTokenKind.SpecificationClause] = typeService.GetClassificationType("Dafny specification clause");
      _typeMap[DafnyTokenKind.BuiltInType] = standards.Keyword;
      _typeMap[DafnyTokenKind.Number] = standards.NumberLiteral;
      _typeMap[DafnyTokenKind.String] = standards.StringLiteral;
      _typeMap[DafnyTokenKind.Char] = standards.StringLiteral;
      _typeMap[DafnyTokenKind.Comment] = standards.Comment;
      _typeMap[DafnyTokenKind.VariableIdentifier] = standards.Identifier;
      _typeMap[DafnyTokenKind.AdditionalInformation] = standards.Other;
      _typeMap[DafnyTokenKind.VariableIdentifierDefinition] = typeService.GetClassificationType("Dafny identifier");
      _typeMap[DafnyTokenKind.Attribute] = typeService.GetClassificationType("Dafny attribute");
      _typeMap[DafnyTokenKind.RecognizedAttributeId] = typeService.GetClassificationType("Dafny recognized attribute");

      if (DafnyMenuPackage == null)
      {
        // Initialize the Dafny menu.
        var shell = Microsoft.VisualStudio.Shell.Package.GetGlobalService(typeof(Microsoft.VisualStudio.Shell.Interop.SVsShell)) as Microsoft.VisualStudio.Shell.Interop.IVsShell;
        if (shell != null)
        {
          Microsoft.VisualStudio.Shell.Interop.IVsPackage package = null;
          Guid PackageToBeLoadedGuid = new Guid("e1baf989-88a6-4acf-8d97-e0dc243476aa");
          if (shell.LoadPackage(ref PackageToBeLoadedGuid, out package) == Microsoft.VisualStudio.VSConstants.S_OK)
          {
            DafnyMenuPackage = (DafnyMenu.DafnyMenuPackage)package;
            DafnyMenuPackage.MenuProxy = new MenuProxy(DafnyMenuPackage);
          }
        }
      }
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
  [ClassificationType(ClassificationTypeNames = "Dafny identifier")]
  [Name("Dafny identifier")]
  [UserVisible(true)]
  //set the priority to be after the default classifiers
  [Order(Before = Priority.Default)]
  internal sealed class DafnyTypeFormat : ClassificationFormatDefinition
  {
    public DafnyTypeFormat() {
      this.DisplayName = "Dafny identifier"; //human readable version of the name
      this.ForegroundColor = Colors.CornflowerBlue;
    }
  }

  internal static class ClassificationDefinition
  {
    /// <summary>
    /// Defines the "ordinary" classification type.
    /// </summary>
    [Export(typeof(ClassificationTypeDefinition))]
    [Name("Dafny identifier")]
    internal static ClassificationTypeDefinition UserType = null;
  }


  /// <summary>
  /// Defines an editor format for user-defined type.
  /// </summary>
  [Export(typeof(EditorFormatDefinition))]
  [ClassificationType(ClassificationTypeNames = "Dafny attribute")]
  [Name("Dafny attribute")]
  [UserVisible(true)]
  //set the priority to be after the default classifiers
  [Order(Before = Priority.Default)]
  internal sealed class DafnyTypeFormat_Attribute : ClassificationFormatDefinition
  {
    public DafnyTypeFormat_Attribute() {
      this.DisplayName = "Dafny attribute"; //human readable version of the name
      this.IsItalic = true;
    }
  }

  internal static class ClassificationDefinition_Attribute
  {
    /// <summary>
    /// Defines the "ordinary" classification type.
    /// </summary>
    [Export(typeof(ClassificationTypeDefinition))]
    [Name("Dafny attribute")]
    internal static ClassificationTypeDefinition UserType = null;
  }

  /// <summary>
  /// Defines an editor format for user-defined type.
  /// </summary>
  [Export(typeof(EditorFormatDefinition))]
  [ClassificationType(ClassificationTypeNames = "Dafny recognized attribute")]
  [Name("Dafny recognized attribute")]
  [UserVisible(true)]
  //set the priority to be after the default classifiers
  [Order(Before = Priority.Default)]
  internal sealed class DafnyTypeFormat_RecognizedAttribute : ClassificationFormatDefinition
  {
    public DafnyTypeFormat_RecognizedAttribute() {
      this.DisplayName = "Dafny recognized attribute"; //human readable version of the name
      this.ForegroundColor = Colors.SaddleBrown;
    }
  }

  internal static class ClassificationDefinition_RecognizedAttribute
  {
    /// <summary>
    /// Defines the "ordinary" classification type.
    /// </summary>
    [Export(typeof(ClassificationTypeDefinition))]
    [Name("Dafny recognized attribute")]
    internal static ClassificationTypeDefinition UserType = null;
  }

  /// <summary>
  /// Defines an editor format for user-defined type.
  /// </summary>
  [Export(typeof(EditorFormatDefinition))]
  [ClassificationType(ClassificationTypeNames = "Dafny specification clause")]
  [Name("Dafny specification clause")]
  [UserVisible(true)]
  //set the priority to be after the default classifiers
  [Order(Before = Priority.Default)]
  internal sealed class DafnyTypeFormat_SpecificationClause : ClassificationFormatDefinition
  {
    public DafnyTypeFormat_SpecificationClause() {
      this.DisplayName = "Dafny specification clause"; //human readable version of the name
      this.ForegroundColor = Colors.Purple;
    }
  }

  internal static class ClassificationDefinition_SpecificationClause
  {
    /// <summary>
    /// Defines the "ordinary" classification type.
    /// </summary>
    [Export(typeof(ClassificationTypeDefinition))]
    [Name("Dafny specification clause")]
    internal static ClassificationTypeDefinition UserType = null;
  }

  #endregion

}
