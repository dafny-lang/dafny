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
  [TagType(typeof(DafnyTokenTag))]
  internal sealed class IdentifierTaggerProvider : ITaggerProvider
  {
    [Import]
    internal IBufferTagAggregatorFactoryService AggregatorFactory = null;

    public ITagger<T> CreateTagger<T>(ITextBuffer buffer) where T : ITag {
      ITagAggregator<DafnyResolverTag> tagAggregator = AggregatorFactory.CreateTagAggregator<DafnyResolverTag>(buffer);
      // create a single tagger for each buffer.
      Func<ITagger<T>> sc = delegate() { return new IdentifierTagger(buffer, tagAggregator) as ITagger<T>; };
      return buffer.Properties.GetOrCreateSingletonProperty<ITagger<T>>(sc);
    }
  }

  /// <summary>
  /// Translate DafnyResolverTag's into IOutliningRegionTag's
  /// </summary>
  internal sealed class IdentifierTagger : ITagger<DafnyTokenTag>
  {
    ITextBuffer _buffer;
    ITextSnapshot _snapshot;  // the most recent snapshot of _buffer that we have been informed about
    Dafny.Program _program;  // the program parsed from _snapshot
    List<IdRegion> _regions = new List<IdRegion>();  // the regions generated from _program
    ITagAggregator<DafnyResolverTag> _aggregator;

    internal IdentifierTagger(ITextBuffer buffer, ITagAggregator<DafnyResolverTag> tagAggregator) {
      _buffer = buffer;
      _snapshot = _buffer.CurrentSnapshot;
      _aggregator = tagAggregator;
      _aggregator.TagsChanged += new EventHandler<TagsChangedEventArgs>(_aggregator_TagsChanged);
    }

    /// <summary>
    /// Find the Error tokens in the set of all tokens and create an ErrorTag for each
    /// </summary>
    public IEnumerable<ITagSpan<DafnyTokenTag>> GetTags(NormalizedSnapshotSpanCollection spans) {
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
      foreach (var r in _regions) {
        if (0 <= r.Length && r.Start <= end && start <= r.Start + r.Length) {
          yield return new TagSpan<DafnyTokenTag>(
            new SnapshotSpan(_snapshot, r.Start, r.Length),
            new DafnyTokenTag(r.IsDefinition ? DafnyTokenKinds.VariableIdentifierDefinition : DafnyTokenKinds.VariableIdentifier, r.HoverText));
        }
      }
    }

    // the Classifier tagger is translating buffer change events into TagsChanged events, so we don't have to
    public event EventHandler<SnapshotSpanEventArgs> TagsChanged;

    void _aggregator_TagsChanged(object sender, TagsChangedEventArgs e) {
      var r = sender as ResolverTagger;
      if (r != null && r._program != null) {
        if (!ComputeIdentifierRegions(r._program, r._snapshot))
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

    bool ComputeIdentifierRegions(Dafny.Program program, ITextSnapshot snapshot) {
      Contract.Requires(snapshot != null);

      if (program == _program)
        return false;  // no new regions

      List<IdRegion> newRegions = new List<IdRegion>();

      foreach (var module in program.Modules) {
        foreach (Dafny.TopLevelDecl d in module.TopLevelDecls) {
          if (!HasBodyTokens(d) && !(d is Dafny.ClassDecl)) {
            continue;
          }
          if (d is Dafny.DatatypeDecl) {
            var dt = (Dafny.DatatypeDecl)d;
            foreach (var ctor in dt.Ctors) {
              foreach (var dtor in ctor.Destructors) {
                if (dtor != null) {
                  newRegions.Add(new IdRegion(dtor.tok, dtor, "destructor", true));
                }
              }
            }
          } else if (d is Dafny.ClassDecl) {
            var cl = (Dafny.ClassDecl)d;
            foreach (var member in cl.Members) {
              if (!HasBodyTokens(member)) {
                continue;
              }
              if (member is Dafny.Function) {
                var f = (Dafny.Function)member;
                foreach (var p in f.Formals) {
                  newRegions.Add(new IdRegion(p.tok, p, true));
                }
                f.Req.ForEach(e => ExprRegions(e, newRegions));
                f.Reads.ForEach(e => ExprRegions(e.E, newRegions));
                f.Ens.ForEach(e => ExprRegions(e, newRegions));
                f.Decreases.Expressions.ForEach(e => ExprRegions(e, newRegions));
                if (f.Body != null) {
                  ExprRegions(f.Body, newRegions);
                }
              } else if (member is Dafny.Method) {
                var m = (Dafny.Method)member;
                foreach (var p in m.Ins) {
                  newRegions.Add(new IdRegion(p.tok, p, true));
                }
                foreach (var p in m.Outs) {
                  newRegions.Add(new IdRegion(p.tok, p, true));
                }
                m.Req.ForEach(e => ExprRegions(e.E, newRegions));
                m.Mod.Expressions.ForEach(e => ExprRegions(e.E, newRegions));
                m.Ens.ForEach(e => ExprRegions(e.E, newRegions));
                m.Decreases.Expressions.ForEach(e => ExprRegions(e, newRegions));
                if (m.Body != null) {
                  StatementRegions(m.Body, newRegions);
                }
              } else if (member is Dafny.Field) {
                var fld = (Dafny.Field)member;
                newRegions.Add(new IdRegion(fld.tok, fld, "field", true));
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

    static void ExprRegions(Dafny.Expression expr, List<IdRegion> regions) {
      Contract.Requires(expr != null);
      Contract.Requires(regions != null);
      if (expr is Dafny.IdentifierExpr) {
        var e = (Dafny.IdentifierExpr)expr;
        regions.Add(new IdRegion(e.tok, e.Var, false));
      } else if (expr is Dafny.FieldSelectExpr) {
        var e = (Dafny.FieldSelectExpr)expr;
        regions.Add(new IdRegion(e.tok, e.Field, "field", false));
      } else if (expr is Dafny.ComprehensionExpr) {
        var e = (Dafny.ComprehensionExpr)expr;
        foreach (var bv in e.BoundVars) {
          regions.Add(new IdRegion(bv.tok, bv, true));
        }
      } else if (expr is Dafny.MatchExpr) {
        var e = (Dafny.MatchExpr)expr;
        foreach (var kase in e.Cases) {
          kase.Arguments.ForEach(bv => regions.Add(new IdRegion(bv.tok, bv, true)));
        }
      } else if (expr is Dafny.ChainingExpression) {
        var e = (Dafny.ChainingExpression)expr;
        // Do the subexpressions only once (that is, avoid the duplication that occurs in the desugared form of the ChainingExpression)
        e.Operands.ForEach(ee => ExprRegions(ee, regions));
        return;  // return here, so as to avoid doing the subexpressions below
      }
      foreach (var ee in expr.SubExpressions) {
        ExprRegions(ee, regions);
      }
    }

    static void StatementRegions(Dafny.Statement stmt, List<IdRegion> regions) {
      Contract.Requires(stmt != null);
      Contract.Requires(regions != null);
      if (stmt is Dafny.VarDecl) {
        var s = (Dafny.VarDecl)stmt;
        regions.Add(new IdRegion(s.Tok, s, true));
      } else if (stmt is Dafny.ParallelStmt) {
        var s = (Dafny.ParallelStmt)stmt;
        s.BoundVars.ForEach(bv => regions.Add(new IdRegion(bv.tok, bv, true)));
      } else if (stmt is Dafny.MatchStmt) {
        var s = (Dafny.MatchStmt)stmt;
        foreach (var kase in s.Cases) {
          kase.Arguments.ForEach(bv => regions.Add(new IdRegion(bv.tok, bv, true)));
        }
      }
      foreach (var ee in stmt.SubExpressions) {
        ExprRegions(ee, regions);
      }
      foreach (var ss in stmt.SubStatements) {
        StatementRegions(ss, regions);
      }
    }

    bool HasBodyTokens(Dafny.Declaration decl) {
      Contract.Requires(decl != null);
      return decl.BodyStartTok != Bpl.Token.NoToken && decl.BodyEndTok != Bpl.Token.NoToken;
    }

    class IdRegion
    {
      public readonly int Start;
      public readonly int Length;
      public readonly string HoverText;
      public readonly bool IsDefinition;
      public IdRegion(Bpl.IToken tok, Dafny.IVariable v, bool isDefinition) {
        Contract.Requires(tok != null);
        Contract.Requires(v != null);
        Start = tok.pos;
        Length = v.Name.Length;
        string kind;
        if (v is Dafny.VarDecl) {
          kind = "local variable";
        } else if (v is Dafny.BoundVar) {
          kind = "bound variable";
        } else {
          var formal = (Dafny.Formal)v;
          kind = formal.InParam ? "in-parameter" : "out-parameter";
        }
        HoverText = string.Format("({2}{3}) {0}: {1}", v.Name, v.Type.ToString(), v.IsGhost ? "ghost " : "", kind);
        IsDefinition = isDefinition;
      }
      public IdRegion(Bpl.IToken tok, Dafny.Field decl, string kind, bool isDefinition) {
        Contract.Requires(tok != null);
        Contract.Requires(decl != null);
        Contract.Requires(kind != null);
        Start = tok.pos;
        Length = decl.Name.Length;
        HoverText = string.Format("({2}{3}) {0}: {1}", decl.FullName, decl.Type.ToString(), decl.IsGhost ? "ghost " : "", kind);
        IsDefinition = isDefinition;
      }
    }
  }

}
