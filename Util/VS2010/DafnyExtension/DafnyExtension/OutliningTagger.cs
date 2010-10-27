//***************************************************************************
// Copyright © 2010 Microsoft Corporation.  All Rights Reserved.
// This code released under the terms of the 
// Microsoft Public License (MS-PL, http://opensource.org/licenses/ms-pl.html.)
//***************************************************************************
using EnvDTE;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.ComponentModel.Composition;
using System.Windows.Threading;
using Microsoft.VisualStudio.Shell;
using Microsoft.VisualStudio.Shell.Interop;
using Microsoft.VisualStudio.Text;
using Microsoft.VisualStudio.Text.Classification;
using Microsoft.VisualStudio.Text.Editor;
using Microsoft.VisualStudio.Text.Tagging;
using Microsoft.VisualStudio.Text.Projection;
using Microsoft.VisualStudio.Utilities;
using Bpl = Microsoft.Boogie;
using Dafny = Microsoft.Dafny;

namespace DafnyLanguage
{
  [Export(typeof(ITaggerProvider))]
  [ContentType("dafny")]
  [TagType(typeof(IOutliningRegionTag))]
  internal sealed class OutliningTaggerProvider : ITaggerProvider
  {
    [Import]
    internal IBufferTagAggregatorFactoryService AggregatorFactory = null;

    public ITagger<T> CreateTagger<T>(ITextBuffer buffer) where T : ITag {
      ITagAggregator<DafnyResolverTag> tagAggregator = AggregatorFactory.CreateTagAggregator<DafnyResolverTag>(buffer);
      // create a single tagger for each buffer.
      Func<ITagger<T>> sc = delegate() { return new OutliningTagger(buffer, tagAggregator) as ITagger<T>; };
      return buffer.Properties.GetOrCreateSingletonProperty<ITagger<T>>(sc);
    }
  }

  /// <summary>
  /// Translate PkgDefTokenTags into ErrorTags and Error List items
  /// </summary>
  internal sealed class OutliningTagger : ITagger<IOutliningRegionTag>
  {
    ITextBuffer _buffer;
    ITagAggregator<DafnyResolverTag> _aggregator;

    internal OutliningTagger(ITextBuffer buffer, ITagAggregator<DafnyResolverTag> tagAggregator) {
      _buffer = buffer;
      _aggregator = tagAggregator;
      _aggregator.TagsChanged += new EventHandler<TagsChangedEventArgs>(_aggregator_TagsChanged);
    }

    /// <summary>
    /// Find the Error tokens in the set of all tokens and create an ErrorTag for each
    /// </summary>
    public IEnumerable<ITagSpan<IOutliningRegionTag>> GetTags(NormalizedSnapshotSpanCollection spans) {
      if (spans.Count == 0) yield break;
      var snapshot = spans[0].Snapshot;
      foreach (var tagSpan in this._aggregator.GetTags(spans)) {
        DafnyResolverTag t = tagSpan.Tag;
        DafnySuccessResolverTag st = t as DafnySuccessResolverTag;
        if (st != null) {
          foreach (Dafny.ModuleDecl module in st.Program.Modules) {
            if (!module.IsDefaultModule) {
              yield return GetOutliningRegionTag(snapshot, module, "module");
            }
            foreach (Dafny.TopLevelDecl d in module.TopLevelDecls) {
              if (d is Dafny.DatatypeDecl) {
                yield return GetOutliningRegionTag(snapshot, d, "datatype");
              } else {
                Dafny.ClassDecl cl = (Dafny.ClassDecl)d;
                if (!cl.IsDefaultClass) {
                  yield return GetOutliningRegionTag(snapshot, cl, "class");
                }
                // do the class members (in particular, functions and methods)
                foreach (Dafny.MemberDecl m in cl.Members) {
                  if (m is Dafny.Function && ((Dafny.Function)m).Body != null) {
                    yield return GetOutliningRegionTag(snapshot, m, "function");
                  } else if (m is Dafny.Method && ((Dafny.Method)m).Body != null) {
                    yield return GetOutliningRegionTag(snapshot, m, "method");
                  }
                }
              }
            }
          }
        }
      }
    }

    TagSpan<OutliningRegionTag> GetOutliningRegionTag(ITextSnapshot snapshot, Dafny.Declaration decl, string kind) {
      int startPosition = decl.BodyStartTok.pos + 1;  // skip the open-curly brace itself
      int length = decl.BodyEndTok.pos - startPosition;
      return new TagSpan<OutliningRegionTag>(
        new SnapshotSpan(snapshot, startPosition, length),
        new OutliningRegionTag(false, false, "...", string.Format("body of {0} {1}", kind, decl.Name)));
    }

    // the Classifier tagger is translating buffer change events into TagsChanged events, so we don't have to
    public event EventHandler<SnapshotSpanEventArgs> TagsChanged;

    void _aggregator_TagsChanged(object sender, TagsChangedEventArgs e) {
      var r = sender as ResolverTagger;
      if (r != null && r._program != null) {
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
  }
}
