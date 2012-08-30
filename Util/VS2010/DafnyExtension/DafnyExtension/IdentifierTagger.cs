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
using Microsoft.Dafny;

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
    Microsoft.Dafny.Program _program;  // the program parsed from _snapshot
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
      if (r != null) {
        ITextSnapshot snap;
        Microsoft.Dafny.Program prog;
        lock (this) {
          snap = r._snapshot;
          prog = r._program;
        }
        if (prog != null) {
          if (!ComputeIdentifierRegions(prog, snap))
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

    bool ComputeIdentifierRegions(Microsoft.Dafny.Program program, ITextSnapshot snapshot) {
      Contract.Requires(snapshot != null);

      if (program == _program)
        return false;  // no new regions

      List<IdRegion> newRegions = new List<IdRegion>();

      foreach (var module in program.Modules) {
        foreach (var d in module.TopLevelDecls) {
          if (d is DatatypeDecl) {
            var dt = (DatatypeDecl)d;
            foreach (var ctor in dt.Ctors) {
              foreach (var dtor in ctor.Destructors) {
                if (dtor != null) {
                  IdRegion.Add(newRegions, dtor.tok, dtor, "destructor", true, module);
                }
              }
            }
          } else if (d is ClassDecl) {
            var cl = (ClassDecl)d;
            foreach (var member in cl.Members) {
              if (member is Function) {
                var f = (Function)member;
                foreach (var p in f.Formals) {
                  IdRegion.Add(newRegions, p.tok, p, true, module);
                }
                f.Req.ForEach(e => ExprRegions(e, newRegions, module));
                f.Reads.ForEach(fe => FrameExprRegions(fe, newRegions, true, module));
                f.Ens.ForEach(e => ExprRegions(e, newRegions, module));
                f.Decreases.Expressions.ForEach(e => ExprRegions(e, newRegions, module));
                if (f.Body != null) {
                  ExprRegions(f.Body, newRegions, module);
                }
              } else if (member is Method) {
                var m = (Method)member;
                foreach (var p in m.Ins) {
                  IdRegion.Add(newRegions, p.tok, p, true, module);
                }
                foreach (var p in m.Outs) {
                  IdRegion.Add(newRegions, p.tok, p, true, module);
                }
                m.Req.ForEach(e => ExprRegions(e.E, newRegions, module));
                m.Mod.Expressions.ForEach(fe => FrameExprRegions(fe, newRegions, true, module));
                m.Ens.ForEach(e => ExprRegions(e.E, newRegions, module));
                m.Decreases.Expressions.ForEach(e => ExprRegions(e, newRegions, module));
                if (m.Body != null) {
                  StatementRegions(m.Body, newRegions, module);
                }
              } else if (member is Field) {
                var fld = (Field)member;
                IdRegion.Add(newRegions, fld.tok, fld, "field", true, module);
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

    static void FrameExprRegions(FrameExpression fe, List<IdRegion> regions, bool descendIntoExpressions, ModuleDefinition module) {
      Contract.Requires(fe != null);
      Contract.Requires(regions != null);
      if (descendIntoExpressions) {
        ExprRegions(fe.E, regions, module);
      }
      if (fe.Field != null) {
        IdRegion.Add(regions, fe.tok, fe.Field, "field", false, module);
      }
    }

    static void ExprRegions(Microsoft.Dafny.Expression expr, List<IdRegion> regions, ModuleDefinition module) {
      Contract.Requires(expr != null);
      Contract.Requires(regions != null);
      if (expr is IdentifierExpr) {
        var e = (IdentifierExpr)expr;
        IdRegion.Add(regions, e.tok, e.Var, false, module);
      } else if (expr is FieldSelectExpr) {
        var e = (FieldSelectExpr)expr;
        IdRegion.Add(regions, e.tok, e.Field, "field", false, module);
      } else if (expr is ComprehensionExpr) {
        var e = (ComprehensionExpr)expr;
        foreach (var bv in e.BoundVars) {
          IdRegion.Add(regions, bv.tok, bv, true, module);
        }
      } else if (expr is MatchExpr) {
        var e = (MatchExpr)expr;
        foreach (var kase in e.Cases) {
          kase.Arguments.ForEach(bv => IdRegion.Add(regions, bv.tok, bv, true, module));
        }
      } else if (expr is ChainingExpression) {
        var e = (ChainingExpression)expr;
        // Do the subexpressions only once (that is, avoid the duplication that occurs in the desugared form of the ChainingExpression)
        e.Operands.ForEach(ee => ExprRegions(ee, regions, module));
        return;  // return here, so as to avoid doing the subexpressions below
      }
      foreach (var ee in expr.SubExpressions) {
        ExprRegions(ee, regions, module);
      }
    }

    static void StatementRegions(Statement stmt, List<IdRegion> regions, ModuleDefinition module) {
      Contract.Requires(stmt != null);
      Contract.Requires(regions != null);
      if (stmt is VarDeclStmt) {
        var s = (VarDeclStmt)stmt;
        // Add the variables here, once, and then go directly to the RHS's (without letting the sub-statements re-do the LHS's)
        foreach (var lhs in s.Lhss) {
          IdRegion.Add(regions, lhs.Tok, lhs, true, module);
        }
        if (s.Update == null) {
          // the VarDeclStmt has no associated assignment
        } else if (s.Update is UpdateStmt) {
          var upd = (UpdateStmt)s.Update;
          foreach (var rhs in upd.Rhss) {
            foreach (var ee in rhs.SubExpressions) {
              ExprRegions(ee, regions, module);
            }
          }
        } else {
          var upd = (AssignSuchThatStmt)s.Update;
          ExprRegions(upd.Expr, regions, module);
        }
        // we're done, so don't do the sub-statements/expressions again
        return;
      } else  if (stmt is VarDecl) {
        var s = (VarDecl)stmt;
        IdRegion.Add(regions, s.Tok, s, true, module);
      } else if (stmt is ParallelStmt) {
        var s = (ParallelStmt)stmt;
        s.BoundVars.ForEach(bv => IdRegion.Add(regions, bv.tok, bv, true, module));
      } else if (stmt is MatchStmt) {
        var s = (MatchStmt)stmt;
        foreach (var kase in s.Cases) {
          kase.Arguments.ForEach(bv => IdRegion.Add(regions, bv.tok, bv, true, module));
        }
      } else if (stmt is LoopStmt) {
        var s = (LoopStmt)stmt;
        if (s.Mod.Expressions != null) {
          s.Mod.Expressions.ForEach(fe => FrameExprRegions(fe, regions, false, module));
        }
      }
      foreach (var ee in stmt.SubExpressions) {
        ExprRegions(ee, regions, module);
      }
      foreach (var ss in stmt.SubStatements) {
        StatementRegions(ss, regions, module);
      }
    }

    class IdRegion
    {
      public readonly int Start;
      public readonly int Length;
      public readonly string HoverText;
      public readonly bool IsDefinition;

      public static void Add(List<IdRegion> regions, Bpl.IToken tok, IVariable v, bool isDefinition, ModuleDefinition context) {
        Contract.Requires(regions != null);
        Contract.Requires(tok != null);
        Contract.Requires(v != null);
        if (!(tok is AutoGeneratedToken)) {
          regions.Add(new IdRegion(tok, v, isDefinition, context));
        }
      }
      public static void Add(List<IdRegion> regions, Bpl.IToken tok, Field decl, string kind, bool isDefinition, ModuleDefinition context) {
        Contract.Requires(regions != null);
        Contract.Requires(tok != null);
        Contract.Requires(decl != null);
        Contract.Requires(kind != null);
        if (!(tok is AutoGeneratedToken)) {
          regions.Add(new IdRegion(tok, decl, kind, isDefinition, context));
        }
      }

      private IdRegion(Bpl.IToken tok, IVariable v, bool isDefinition, ModuleDefinition context) {
        Contract.Requires(tok != null);
        Contract.Requires(v != null);
        Start = tok.pos;
        Length = v.Name.Length;
        string kind;
        if (v is VarDecl) {
          kind = "local variable";
        } else if (v is BoundVar) {
          kind = "bound variable";
        } else {
          var formal = (Formal)v;
          kind = formal.InParam ? "in-parameter" : "out-parameter";
        }
        HoverText = string.Format("({2}{3}) {0}: {1}", v.Name, v.Type.TypeName(context), v.IsGhost ? "ghost " : "", kind);
        IsDefinition = isDefinition;
      }
      private IdRegion(Bpl.IToken tok, Field decl, string kind, bool isDefinition, ModuleDefinition context) {
        Contract.Requires(tok != null);
        Contract.Requires(decl != null);
        Contract.Requires(kind != null);
        Start = tok.pos;
        Length = decl.Name.Length;
        HoverText = string.Format("({2}{3}) {0}: {1}", decl.FullNameInContext(context), decl.Type.TypeName(context), decl.IsGhost ? "ghost " : "", kind);
        IsDefinition = isDefinition;
      }
    }
  }

}
