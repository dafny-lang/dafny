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
using System.Diagnostics.Contracts;
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
    ITextSnapshot _snapshot;  // the most recent snapshot of _buffer that we have been informed about
    Dafny.Program _program;  // the program parsed from _snapshot
    List<ORegion> _regions = new List<ORegion>();  // the regions generated from _program
    ITagAggregator<DafnyResolverTag> _aggregator;

    internal OutliningTagger(ITextBuffer buffer, ITagAggregator<DafnyResolverTag> tagAggregator) {
      _buffer = buffer;
      _snapshot = _buffer.CurrentSnapshot;
      _aggregator = tagAggregator;
      _aggregator.TagsChanged += new EventHandler<TagsChangedEventArgs>(_aggregator_TagsChanged);
    }

    /// <summary>
    /// Find the Error tokens in the set of all tokens and create an ErrorTag for each
    /// </summary>
    public IEnumerable<ITagSpan<IOutliningRegionTag>> GetTags(NormalizedSnapshotSpanCollection spans) {
      if (spans.Count == 0) yield break;
      // (A NormalizedSnapshotSpanCollection contains spans that all come from the same snapshot.)
      // The spans are ordered by the .Start component, and the collection contains no adjacent or abutting spans.
      // Hence, to find a span that includes all the ones in "spans", we only need to look at the .Start for the
      // first spand and the .End of the last span:
      var startPoint = spans[0].Start;
      var endPoint = spans[spans.Count - 1].End;

      // Note, (startPoint,endPoint) are points in the spans for which we're being asked to provide tags.  We need to translate
      // these back into the most recent snapshot that we've computed regions for, namely _snapshot.
      var entire = new SnapshotSpan(startPoint, endPoint).TranslateTo(_snapshot, SpanTrackingMode.EdgeExclusive);
      int start = entire.Start;
      int end = entire.End;
      if (start == end) yield break;

      foreach (var r in _regions) {
        if (0 <= r.Length && r.Start <= end && start <= r.Start + r.Length) {
          yield return new TagSpan<OutliningRegionTag>(
            new SnapshotSpan(_snapshot, r.Start, r.Length),
            new OutliningRegionTag(false, false, "...", r.HoverText));
        }
      }
    }

    // the Classifier tagger is translating buffer change events into TagsChanged events, so we don't have to
    public event EventHandler<SnapshotSpanEventArgs> TagsChanged;

    void _aggregator_TagsChanged(object sender, TagsChangedEventArgs e) {
      var r = sender as ResolverTagger;
      if (r != null) {
        ITextSnapshot snap;
        Microsoft.Dafny.Program prog;
        lock (this) {
          snap = r._snapshot;
          prog = r._program;
        }
        if (prog != null) {
          if (!ComputeOutliningRegions(prog, snap))
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
    }

    bool ComputeOutliningRegions(Dafny.Program program, ITextSnapshot snapshot) {
      Contract.Requires(snapshot != null);

      if (program == _program)
        return false;  // no new regions

      List<ORegion> newRegions = new List<ORegion>();

      foreach (var module in program.Modules) {
        if (!module.IsDefaultModule) {
          newRegions.Add(new ORegion(module, "module"));
        }
        foreach (Dafny.TopLevelDecl d in module.TopLevelDecls) {
          if (!HasBodyTokens(d) && !(d is Dafny.ClassDecl)) {
            continue;
          }
          if (d is Dafny.ArbitraryTypeDecl) {
            newRegions.Add(new ORegion(d, "type"));
          } else if (d is Dafny.CoDatatypeDecl) {
            newRegions.Add(new ORegion(d, "codatatype"));
          } else if (d is Dafny.DatatypeDecl) {
            newRegions.Add(new ORegion(d, "datatype"));
          } else if (d is Dafny.ModuleDecl) {
            // do nothing here, since the outer loop handles modules
          } else {
            Dafny.ClassDecl cl = (Dafny.ClassDecl)d;
            if (!cl.IsDefaultClass) {
              newRegions.Add(new ORegion(cl, "class"));
            }
            // do the class members (in particular, functions and methods)
            foreach (Dafny.MemberDecl m in cl.Members) {
              if (!HasBodyTokens(m)) {
                continue;
              }
              if (m is Dafny.Function && ((Dafny.Function)m).Body != null) {
                var nm =
                  m is Dafny.CoPredicate ? "copredicate" :
                  m is Dafny.PrefixPredicate ? "prefix predicate" :
                  m is Dafny.Predicate ? "predicate" :
                  "function";
                newRegions.Add(new ORegion(m, nm));
              } else if (m is Dafny.Method && ((Dafny.Method)m).Body != null) {
                var nm =
                  m is Dafny.Constructor ? "constructor" :
                  m is Dafny.PrefixMethod ? "prefix method" :
                  "method";
                newRegions.Add(new ORegion(m, nm));
              }
            }
          }
        }
      }
      _snapshot = snapshot;
      _regions = newRegions;
      _program = program;
      return true;
    }

    bool HasBodyTokens(Dafny.Declaration decl) {
      Contract.Requires(decl != null);
      return decl.BodyStartTok != Bpl.Token.NoToken && decl.BodyEndTok != Bpl.Token.NoToken;
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
