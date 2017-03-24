using System;
using System.Collections.Generic;
using System.ComponentModel.Composition;
using System.Diagnostics.Contracts;
using Microsoft.VisualStudio.Text;
using Microsoft.VisualStudio.Text.Tagging;
using Microsoft.VisualStudio.Utilities;
using Bpl = Microsoft.Boogie;
using Dafny = Microsoft.Dafny;


namespace DafnyLanguage
{

  #region Provider

  [Export(typeof(ITaggerProvider))]
  [ContentType("dafny")]
  [TagType(typeof(IOutliningRegionTag))]
  internal sealed class OutliningTaggerProvider : ITaggerProvider
  {
    [Import]
    internal IBufferTagAggregatorFactoryService AggregatorFactory = null;

    public ITagger<T> CreateTagger<T>(ITextBuffer buffer) where T : ITag {
      ITagAggregator<IDafnyResolverTag> tagAggregator = AggregatorFactory.CreateTagAggregator<IDafnyResolverTag>(buffer);
      // create a single tagger for each buffer.
      Func<ITagger<T>> sc = delegate() { return new OutliningTagger(buffer, tagAggregator) as ITagger<T>; };
      return buffer.Properties.GetOrCreateSingletonProperty<ITagger<T>>(sc);
    }
  }

  #endregion


  #region Tagger

  /// <summary>
  /// Translate DafnyResolverTag's into IOutliningRegionTag's
  /// </summary>
  internal sealed class OutliningTagger : ITagger<IOutliningRegionTag>
  {
    ITextBuffer _buffer;
    ITextSnapshot _snapshot;  // the most recent snapshot of _buffer that we have been informed about
    Dafny.Program _program;  // the program parsed from _snapshot
    List<OutliningRegion> _regions = new List<OutliningRegion>();  // the regions generated from _program
    ITagAggregator<IDafnyResolverTag> _aggregator;

    internal OutliningTagger(ITextBuffer buffer, ITagAggregator<IDafnyResolverTag> tagAggregator) {
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
          snap = r.Snapshot;
          prog = r.Program;
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

      List<OutliningRegion> newRegions = new List<OutliningRegion>();

      foreach (var module in program.Modules()) {
        if (!module.IsDefaultModule) {
          var nm = "module";
          if (module.IsAbstract) {
            nm = "abstract " + nm;
          }
          OutliningRegion.Add(newRegions, program, module, nm);
        }
        foreach (Dafny.TopLevelDecl d in module.TopLevelDecls) {
          if (!HasBodyTokens(d) && !(d is Dafny.ClassDecl)) {
            continue;
          }
          if (d is Dafny.OpaqueTypeDecl) {
            OutliningRegion.Add(newRegions, program, d, "type");
          } else if (d is Dafny.CoDatatypeDecl) {
            OutliningRegion.Add(newRegions, program, d, "codatatype");
          } else if (d is Dafny.DatatypeDecl) {
            OutliningRegion.Add(newRegions, program, d, "datatype");
          } else if (d is Dafny.ModuleDecl) {
            // do nothing here, since the outer loop handles modules
          } else {
            var cl = (Dafny.ClassDecl)d;
            if (cl.IsDefaultClass) {
              // do nothing
            } else if (cl is Dafny.IteratorDecl) {
              OutliningRegion.Add(newRegions, program, cl, "iterator");
            } else {
              OutliningRegion.Add(newRegions, program, cl, "class");
            }
            // do the class members (in particular, functions and methods)
            foreach (Dafny.MemberDecl m in cl.Members) {
              if (!HasBodyTokens(m)) {
                continue;
              }
              if (m is Dafny.Function && ((Dafny.Function)m).Body != null) {
                var nm =
                  m is Dafny.InductivePredicate ? "inductive predicate" :
                  m is Dafny.CoPredicate ? "copredicate" :
                  // m is Dafny.PrefixPredicate ? "prefix predicate" :  // this won't ever occur here
                  m is Dafny.Predicate ? "predicate" :
                  "function";
                if (!m.IsGhost) {
                  nm += " method";
                }
                OutliningRegion.Add(newRegions, program, m, nm);
              } else if (m is Dafny.Method && ((Dafny.Method)m).Body != null) {
                var nm =
                  m is Dafny.Constructor ? "constructor" :
                  m is Dafny.CoLemma ? "colemma" :
                  m is Dafny.Lemma ? "lemma" :
                  // m is Dafny.PrefixLemma ? "prefix lemma" :  // this won't ever occur here
                  "method";
                if (m.IsGhost && !(m is Dafny.CoLemma)) {
                  nm = "ghost " + nm;
                }
                OutliningRegion.Add(newRegions, program, m, nm);
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

    static bool HasBodyTokens(Dafny.Declaration decl) {
      Contract.Requires(decl != null);
      return decl.BodyStartTok != Bpl.Token.NoToken && decl.BodyEndTok != Bpl.Token.NoToken;
    }

    class OutliningRegion : DafnyRegion
    {
      public static void Add(List<OutliningRegion> regions, Microsoft.Dafny.Program prog, Dafny.INamedRegion decl, string kind) {
        Contract.Requires(regions != null);
        Contract.Requires(prog != null);
        if (InMainFileAndUserDefined(prog, decl.BodyStartTok)) {
          regions.Add(new OutliningRegion(decl, kind));
        }
      }

      public readonly int Start;
      public readonly int Length;
      public readonly string HoverText;
      private OutliningRegion(Dafny.INamedRegion decl, string kind) {
        int startPosition = decl.BodyStartTok.pos + 1;  // skip the open-curly brace itself
        int length = decl.BodyEndTok.pos - startPosition;
        Start = startPosition;
        Length = length;
        HoverText = string.Format("body of {0} {1}", kind, decl.Name);
      }
    }
  }

  #endregion

}
