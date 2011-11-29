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
  /// Translate DafnyResolverTag's into IOutliningRegionTag's
  /// </summary>
  internal sealed class OutliningTagger : ITagger<IOutliningRegionTag>
  {
    ITextBuffer _buffer;
    ITagAggregator<DafnyResolverTag> _aggregator;
    Dafny.Program _program;
    List<ORegion> _regions = new List<ORegion>();

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
      foreach (var r in _regions) {
        yield return new TagSpan<OutliningRegionTag>(
          new SnapshotSpan(snapshot, r.Start, r.Length),
          new OutliningRegionTag(false, false, "...", r.HoverText));
      }
    }

    // the Classifier tagger is translating buffer change events into TagsChanged events, so we don't have to
    public event EventHandler<SnapshotSpanEventArgs> TagsChanged;

    void _aggregator_TagsChanged(object sender, TagsChangedEventArgs e) {
      var r = sender as ResolverTagger;
      if (r != null && r._program != null) {
        if (!ComputeOutliningRegions(r._program))
          return;  // no new regions

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

    bool ComputeOutliningRegions(Dafny.Program program) {
      if (program == _program)
        return false;  // no new regions

      List<ORegion> newRegions = new List<ORegion>();

      foreach (Dafny.ModuleDecl module in program.Modules) {
        if (!module.IsDefaultModule) {
          newRegions.Add(new ORegion(module, "module"));
        }
        foreach (Dafny.TopLevelDecl d in module.TopLevelDecls) {
          if (d is Dafny.DatatypeDecl) {
            newRegions.Add(new ORegion(d, "datatype"));
          } else {
            Dafny.ClassDecl cl = (Dafny.ClassDecl)d;
            if (!cl.IsDefaultClass) {
              newRegions.Add(new ORegion(cl, "class"));
            }
            // do the class members (in particular, functions and methods)
            foreach (Dafny.MemberDecl m in cl.Members) {
              if (m is Dafny.Function && ((Dafny.Function)m).Body != null) {
                newRegions.Add(new ORegion(m, "function"));
              } else if (m is Dafny.Method && ((Dafny.Method)m).Body != null) {
                newRegions.Add(new ORegion(m, "method"));
              }
            }
          }
        }
      }
      _regions = newRegions;
      _program = program;
      return true;
    }

    class ORegion
    {
      public readonly int Start;
      public readonly int Length;
      public readonly string HoverText;
      public ORegion(Dafny.Declaration decl, string kind) {
        int startPosition = decl.BodyStartTok.pos + 1;  // skip the open-curly brace itself
        int length = decl.BodyEndTok.pos - startPosition;
        Start = startPosition;
        Length = length;
        HoverText = string.Format("body of {0} {1}", kind, decl.Name);
      }
    }
  }
}
