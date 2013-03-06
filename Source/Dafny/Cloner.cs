
using System;
using System.Collections.Generic;
using System.Numerics;
using System.Diagnostics.Contracts;
using IToken = Microsoft.Boogie.IToken;

namespace Microsoft.Dafny
{
  class Cloner
  {
    public ModuleDefinition CloneModuleDefinition(ModuleDefinition m, string name) {
      ModuleDefinition nw;
      if (m is DefaultModuleDecl) {
        nw = new DefaultModuleDecl();
      } else {
        nw = new ModuleDefinition(Tok(m.tok), name, m.IsAbstract, m.IsFacade, m.RefinementBaseName, CloneAttributes(m.Attributes), true);
      }
      foreach (var d in m.TopLevelDecls) {
        nw.TopLevelDecls.Add(CloneDeclaration(d, nw));
      }
      nw.RefinementBase = m.RefinementBase;
      nw.Height = m.Height;
      return nw;
    }
    public TopLevelDecl CloneDeclaration(TopLevelDecl d, ModuleDefinition m) {
      Contract.Requires(d != null);
      Contract.Requires(m != null);

      if (d is ArbitraryTypeDecl) {
        var dd = (ArbitraryTypeDecl)d;
        return new ArbitraryTypeDecl(Tok(dd.tok), dd.Name, m, dd.EqualitySupport, CloneAttributes(dd.Attributes));
      } else if (d is IndDatatypeDecl) {
        var dd = (IndDatatypeDecl)d;
        var tps = dd.TypeArgs.ConvertAll(CloneTypeParam);
        var ctors = dd.Ctors.ConvertAll(CloneCtor);
        var dt = new IndDatatypeDecl(Tok(dd.tok), dd.Name, m, tps, ctors, CloneAttributes(dd.Attributes));
        return dt;
      } else if (d is CoDatatypeDecl) {
        var dd = (CoDatatypeDecl)d;
        var tps = dd.TypeArgs.ConvertAll(CloneTypeParam);
        var ctors = dd.Ctors.ConvertAll(CloneCtor);
        var dt = new CoDatatypeDecl(Tok(dd.tok), dd.Name, m, tps, ctors, CloneAttributes(dd.Attributes));
        return dt;
      } else if (d is IteratorDecl) {
        var dd = (IteratorDecl)d;
        var tps = dd.TypeArgs.ConvertAll(CloneTypeParam);
        var ins = dd.Ins.ConvertAll(CloneFormal);
        var outs = dd.Outs.ConvertAll(CloneFormal);
        var reads = CloneSpecFrameExpr(dd.Reads);
        var mod = CloneSpecFrameExpr(dd.Modifies);
        var decr = CloneSpecExpr(dd.Decreases);
        var req = dd.Requires.ConvertAll(CloneMayBeFreeExpr);
        var yreq = dd.YieldRequires.ConvertAll(CloneMayBeFreeExpr);
        var ens = dd.Ensures.ConvertAll(CloneMayBeFreeExpr);
        var yens = dd.YieldEnsures.ConvertAll(CloneMayBeFreeExpr);
        var body = CloneBlockStmt(dd.Body);
        var iter = new IteratorDecl(Tok(dd.tok), dd.Name, dd.Module,
          tps, ins, outs, reads, mod, decr,
          req, ens, yreq, yens,
          body, CloneAttributes(dd.Attributes), dd.SignatureIsOmitted);
        return iter;
      } else if (d is ClassDecl) {
        if (d is DefaultClassDecl) {
          var dd = (ClassDecl)d;
          var tps = dd.TypeArgs.ConvertAll(CloneTypeParam);
          var mm = dd.Members.ConvertAll(CloneMember);
          var cl = new DefaultClassDecl(m, mm);
          return cl;
        } else {
          var dd = (ClassDecl)d;
          var tps = dd.TypeArgs.ConvertAll(CloneTypeParam);
          var mm = dd.Members.ConvertAll(CloneMember);
          var cl = new ClassDecl(Tok(dd.tok), dd.Name, m, tps, mm, CloneAttributes(dd.Attributes));
          return cl;
        }
      } else if (d is ModuleDecl) {
        if (d is LiteralModuleDecl) {
          var l = new LiteralModuleDecl(((LiteralModuleDecl)d).ModuleDef, m);
          l.Signature = ((ModuleDecl)d).Signature;
          return l;
        } else if (d is AliasModuleDecl) {
          var a = (AliasModuleDecl)d;
          var alias = new AliasModuleDecl(a.Path, a.tok, m, a.Opened);
          alias.ModuleReference = a.ModuleReference;
          alias.Signature = a.Signature;
          return alias;
        } else if (d is ModuleFacadeDecl) {
          var a = (ModuleFacadeDecl)d;
          var abs = new ModuleFacadeDecl(a.Path, a.tok, m, a.CompilePath, a.Opened);
          abs.Signature = a.Signature;
          abs.OriginalSignature = a.OriginalSignature;
          return abs;
        } else {
          Contract.Assert(false);  // unexpected declaration
          return null;  // to please compiler
        }
      } else {
        Contract.Assert(false);  // unexpected declaration
        return null;  // to please compiler
      }
    }

    public DatatypeCtor CloneCtor(DatatypeCtor ct) {
      return new DatatypeCtor(Tok(ct.tok), ct.Name, ct.Formals.ConvertAll(CloneFormal), CloneAttributes(ct.Attributes));
    }

    public TypeParameter CloneTypeParam(TypeParameter tp) {
      return new TypeParameter(Tok(tp.tok), tp.Name, tp.EqualitySupport);
    }

    public MemberDecl CloneMember(MemberDecl member) {
      if (member is Field) {
        Contract.Assert(!(member is SpecialField));  // we don't expect a SpecialField to be cloned (or do we?)
        var f = (Field)member;
        return new Field(Tok(f.tok), f.Name, f.IsGhost, f.IsMutable, f.IsUserMutable, CloneType(f.Type), CloneAttributes(f.Attributes));
      } else if (member is Function) {
        var f = (Function)member;
        return CloneFunction(f);
      } else {
        var m = (Method)member;
        return CloneMethod(m);
      }
    }

    public Type CloneType(Type t) {
      if (t is BasicType) {
        return t;
      } else if (t is SetType) {
        var tt = (SetType)t;
        return new SetType(CloneType(tt.Arg));
      } else if (t is SeqType) {
        var tt = (SeqType)t;
        return new SeqType(CloneType(tt.Arg));
      } else if (t is MultiSetType) {
        var tt = (MultiSetType)t;
        return new MultiSetType(CloneType(tt.Arg));
      } else if (t is MapType) {
        var tt = (MapType)t;
        return new MapType(CloneType(tt.Domain), CloneType(tt.Range));
      } else if (t is UserDefinedType) {
        var tt = (UserDefinedType)t;
        return new UserDefinedType(Tok(tt.tok), tt.Name, tt.TypeArgs.ConvertAll(CloneType), tt.Path.ConvertAll(Tok));
      } else if (t is InferredTypeProxy) {
        return new InferredTypeProxy();
      } else if (t is ParamTypeProxy) {
        return new ParamTypeProxy(CloneTypeParam(((ParamTypeProxy)t).orig));
      } else {
        Contract.Assert(false);  // unexpected type (e.g., no other type proxies are expected at this time)
        return null;  // to please compiler
      }
    }

    public Formal CloneFormal(Formal formal) {
      return new Formal(Tok(formal.tok), formal.Name, CloneType(formal.Type), formal.InParam, formal.IsGhost);
    }

    public BoundVar CloneBoundVar(BoundVar bv) {
      return new BoundVar(Tok(bv.tok), bv.Name, CloneType(bv.Type));
    }

    public Specification<Expression> CloneSpecExpr(Specification<Expression> spec) {
      var ee = spec.Expressions == null ? null : spec.Expressions.ConvertAll(CloneExpr);
      return new Specification<Expression>(ee, CloneAttributes(spec.Attributes));
    }

    public Specification<FrameExpression> CloneSpecFrameExpr(Specification<FrameExpression> frame) {
      var ee = frame.Expressions == null ? null : frame.Expressions.ConvertAll(CloneFrameExpr);
      return new Specification<FrameExpression>(ee, CloneAttributes(frame.Attributes));
    }

    public FrameExpression CloneFrameExpr(FrameExpression frame) {
      return new FrameExpression(Tok(frame.tok), CloneExpr(frame.E), frame.FieldName);
    }
    public Attributes CloneAttributes(Attributes attrs) {
      if (attrs == null) {
        return null;
      } else {
        return new Attributes(attrs.Name, attrs.Args.ConvertAll(CloneAttrArg), CloneAttributes(attrs.Prev));
      }
    }
    public Attributes.Argument CloneAttrArg(Attributes.Argument aa) {
      if (aa.E != null) {
        return new Attributes.Argument(Tok(aa.Tok), CloneExpr(aa.E));
      } else {
        return new Attributes.Argument(Tok(aa.Tok), aa.S);
      }
    }

    public MaybeFreeExpression CloneMayBeFreeExpr(MaybeFreeExpression expr) {
      var mfe = new MaybeFreeExpression(CloneExpr(expr.E), expr.IsFree);
      mfe.Attributes = CloneAttributes(expr.Attributes);
      return mfe;
    }

    public virtual Expression CloneExpr(Expression expr) {
      if (expr == null) {
        return null;
      } else if (expr is LiteralExpr) {
        var e = (LiteralExpr)expr;
        if (e.Value == null) {
          return new LiteralExpr(Tok(e.tok));
        } else if (e.Value is bool) {
          return new LiteralExpr(Tok(e.tok), (bool)e.Value);
        } else {
          return new LiteralExpr(Tok(e.tok), (BigInteger)e.Value);
        }

      } else if (expr is ThisExpr) {
        if (expr is ImplicitThisExpr) {
          return new ImplicitThisExpr(Tok(expr.tok));
        } else {
          return new ThisExpr(Tok(expr.tok));
        }

      } else if (expr is IdentifierExpr) {
        var e = (IdentifierExpr)expr;
        return new IdentifierExpr(Tok(e.tok), e.Name);

      } else if (expr is DatatypeValue) {
        var e = (DatatypeValue)expr;
        return new DatatypeValue(Tok(e.tok), e.DatatypeName, e.MemberName, e.Arguments.ConvertAll(CloneExpr));

      } else if (expr is DisplayExpression) {
        DisplayExpression e = (DisplayExpression)expr;
        if (expr is SetDisplayExpr) {
          return new SetDisplayExpr(Tok(e.tok), e.Elements.ConvertAll(CloneExpr));
        } else if (expr is MultiSetDisplayExpr) {
          return new MultiSetDisplayExpr(Tok(e.tok), e.Elements.ConvertAll(CloneExpr));
        } else {
          Contract.Assert(expr is SeqDisplayExpr);
          return new SeqDisplayExpr(Tok(e.tok), e.Elements.ConvertAll(CloneExpr));
        }

      } else if (expr is MapDisplayExpr) {
        MapDisplayExpr e = (MapDisplayExpr)expr;
        List<ExpressionPair> pp = new List<ExpressionPair>();
        foreach (ExpressionPair p in e.Elements) {
          pp.Add(new ExpressionPair(CloneExpr(p.A), CloneExpr(p.B)));
        }
        return new MapDisplayExpr(Tok(expr.tok), pp);
      } else if (expr is ExprDotName) {
        var e = (ExprDotName)expr;
        return new ExprDotName(Tok(e.tok), CloneExpr(e.Obj), e.SuffixName);

      } else if (expr is FieldSelectExpr) {
        var e = (FieldSelectExpr)expr;
        return new FieldSelectExpr(Tok(e.tok), CloneExpr(e.Obj), e.FieldName);

      } else if (expr is SeqSelectExpr) {
        var e = (SeqSelectExpr)expr;
        return new SeqSelectExpr(Tok(e.tok), e.SelectOne, CloneExpr(e.Seq), CloneExpr(e.E0), CloneExpr(e.E1));

      } else if (expr is MultiSelectExpr) {
        var e = (MultiSelectExpr)expr;
        return new MultiSelectExpr(Tok(e.tok), CloneExpr(e.Array), e.Indices.ConvertAll(CloneExpr));

      } else if (expr is SeqUpdateExpr) {
        var e = (SeqUpdateExpr)expr;
        return new SeqUpdateExpr(Tok(e.tok), CloneExpr(e.Seq), CloneExpr(e.Index), CloneExpr(e.Value));

      } else if (expr is FunctionCallExpr) {
        var e = (FunctionCallExpr)expr;
        return new FunctionCallExpr(Tok(e.tok), e.Name, CloneExpr(e.Receiver), e.OpenParen == null ? null : Tok(e.OpenParen), e.Args.ConvertAll(CloneExpr));

      } else if (expr is OldExpr) {
        var e = (OldExpr)expr;
        return new OldExpr(Tok(e.tok), CloneExpr(e.E));

      } else if (expr is MultiSetFormingExpr) {
        var e = (MultiSetFormingExpr)expr;
        return new MultiSetFormingExpr(Tok(e.tok), CloneExpr(e.E));

      } else if (expr is FreshExpr) {
        var e = (FreshExpr)expr;
        return new FreshExpr(Tok(e.tok), CloneExpr(e.E));

      } else if (expr is UnaryExpr) {
        var e = (UnaryExpr)expr;
        return new UnaryExpr(Tok(e.tok), e.Op, CloneExpr(e.E));

      } else if (expr is BinaryExpr) {
        var e = (BinaryExpr)expr;
        return new BinaryExpr(Tok(e.tok), e.Op, CloneExpr(e.E0), CloneExpr(e.E1));

      } else if (expr is TernaryExpr) {
        var e = (TernaryExpr)expr;
        return new TernaryExpr(Tok(e.tok), e.Op, CloneExpr(e.E0), CloneExpr(e.E1), CloneExpr(e.E2));

      } else if (expr is ChainingExpression) {
        var e = (ChainingExpression)expr;
        return CloneExpr(e.E);  // just clone the desugaring, since it's already available

      } else if (expr is LetExpr) {
        var e = (LetExpr)expr;
        return new LetExpr(Tok(e.tok), e.Vars.ConvertAll(CloneBoundVar), e.RHSs.ConvertAll(CloneExpr), CloneExpr(e.Body), e.Exact);

      } else if (expr is NamedExpr) {
        var e = (NamedExpr)expr;
        return new NamedExpr(Tok(e.tok), e.Name, CloneExpr(e.Body));
      } else if (expr is ComprehensionExpr) {
        var e = (ComprehensionExpr)expr;
        var tk = Tok(e.tok);
        var bvs = e.BoundVars.ConvertAll(CloneBoundVar);
        var range = CloneExpr(e.Range);
        var term = CloneExpr(e.Term);
        if (e is ForallExpr) {
          return new ForallExpr(tk, bvs, range, term, CloneAttributes(e.Attributes));
        } else if (e is ExistsExpr) {
          return new ExistsExpr(tk, bvs, range, term, CloneAttributes(e.Attributes));
        } else if (e is MapComprehension) {
          return new MapComprehension(tk, bvs, range, term);
        } else {
          Contract.Assert(e is SetComprehension);
          return new SetComprehension(tk, bvs, range, term);
        }

      } else if (expr is WildcardExpr) {
        return new WildcardExpr(Tok(expr.tok));

      } else if (expr is PredicateExpr) {
        var e = (PredicateExpr)expr;
        if (e is AssertExpr) {
          return new AssertExpr(Tok(e.tok), CloneExpr(e.Guard), CloneExpr(e.Body));
        } else {
          Contract.Assert(e is AssumeExpr);
          return new AssumeExpr(Tok(e.tok), CloneExpr(e.Guard), CloneExpr(e.Body));
        }

      } else if (expr is CalcExpr) {
        var e = (CalcExpr)expr;
        return new CalcExpr(Tok(e.tok), (CalcStmt)CloneStmt(e.Guard), CloneExpr(e.Body), (AssumeExpr)CloneExpr(e.AsAssumeExpr));

      } else if (expr is ITEExpr) {
        var e = (ITEExpr)expr;
        return new ITEExpr(Tok(e.tok), CloneExpr(e.Test), CloneExpr(e.Thn), CloneExpr(e.Els));

      } else if (expr is ParensExpression) {
        var e = (ParensExpression)expr;
        return CloneExpr(e.E);  // skip the parentheses in the clone

      } else if (expr is IdentifierSequence) {
        var e = (IdentifierSequence)expr;
        var aa = e.Arguments == null ? null : e.Arguments.ConvertAll(CloneExpr);
        return new IdentifierSequence(e.Tokens.ConvertAll(Tok), e.OpenParen == null ? null : Tok(e.OpenParen), aa);

      } else if (expr is MatchExpr) {
        var e = (MatchExpr)expr;
        return new MatchExpr(Tok(e.tok), CloneExpr(e.Source),
          e.Cases.ConvertAll(c => new MatchCaseExpr(Tok(c.tok), c.Id, c.Arguments.ConvertAll(CloneBoundVar), CloneExpr(c.Body))));

      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected expression
      }
    }

    public AssignmentRhs CloneRHS(AssignmentRhs rhs) {
      AssignmentRhs c;
      if (rhs is ExprRhs) {
        var r = (ExprRhs)rhs;
        c = new ExprRhs(CloneExpr(r.Expr));
      } else if (rhs is HavocRhs) {
        c = new HavocRhs(Tok(rhs.Tok));
      } else {
        var r = (TypeRhs)rhs;
        if (r.ArrayDimensions != null) {
          c = new TypeRhs(Tok(r.Tok), CloneType(r.EType), r.ArrayDimensions.ConvertAll(CloneExpr));
        } else if (r.Arguments == null) {
          c = new TypeRhs(Tok(r.Tok), CloneType(r.EType));
        } else {
          c = new TypeRhs(Tok(r.Tok), CloneType(r.EType), r.OptionalNameComponent, CloneExpr(r.ReceiverArgumentForInitCall), r.Arguments.ConvertAll(CloneExpr));
        }
      }
      c.Attributes = CloneAttributes(rhs.Attributes);
      return c;
    }

    public BlockStmt CloneBlockStmt(BlockStmt stmt) {
      if (stmt == null) {
        return null;
      } else {
        return new BlockStmt(Tok(stmt.Tok), stmt.Body.ConvertAll(CloneStmt));
      }
    }

    public virtual Statement CloneStmt(Statement stmt) {
      if (stmt == null) {
        return null;
      }

      Statement r;
      if (stmt is AssertStmt) {
        var s = (AssertStmt)stmt;
        r = new AssertStmt(Tok(s.Tok), CloneExpr(s.Expr), null);

      } else if (stmt is AssumeStmt) {
        var s = (AssumeStmt)stmt;
        r = new AssumeStmt(Tok(s.Tok), CloneExpr(s.Expr), null);

      } else if (stmt is PrintStmt) {
        var s = (PrintStmt)stmt;
        r = new PrintStmt(Tok(s.Tok), s.Args.ConvertAll(CloneAttrArg));

      } else if (stmt is BreakStmt) {
        var s = (BreakStmt)stmt;
        if (s.TargetLabel != null) {
          r = new BreakStmt(Tok(s.Tok), s.TargetLabel);
        } else {
          r = new BreakStmt(Tok(s.Tok), s.BreakCount);
        }

      } else if (stmt is ReturnStmt) {
        var s = (ReturnStmt)stmt;
        r = new ReturnStmt(Tok(s.Tok), s.rhss == null ? null : s.rhss.ConvertAll(CloneRHS));

      } else if (stmt is YieldStmt) {
        var s = (YieldStmt)stmt;
        r = new YieldStmt(Tok(s.Tok), s.rhss == null ? null : s.rhss.ConvertAll(CloneRHS));

      } else if (stmt is AssignStmt) {
        var s = (AssignStmt)stmt;
        r = new AssignStmt(Tok(s.Tok), CloneExpr(s.Lhs), CloneRHS(s.Rhs));

      } else if (stmt is VarDecl) {
        var s = (VarDecl)stmt;
        r = new VarDecl(Tok(s.Tok), s.Name, CloneType(s.OptionalType), s.IsGhost);

      } else if (stmt is CallStmt) {
        var s = (CallStmt)stmt;
        r = new CallStmt(Tok(s.Tok), s.Lhs.ConvertAll(CloneExpr), CloneExpr(s.Receiver), s.MethodName, s.Args.ConvertAll(CloneExpr));

      } else if (stmt is BlockStmt) {
        r = CloneBlockStmt((BlockStmt)stmt);

      } else if (stmt is IfStmt) {
        var s = (IfStmt)stmt;
        r = new IfStmt(Tok(s.Tok), CloneExpr(s.Guard), CloneBlockStmt(s.Thn), CloneStmt(s.Els));

      } else if (stmt is AlternativeStmt) {
        var s = (AlternativeStmt)stmt;
        r = new AlternativeStmt(Tok(s.Tok), s.Alternatives.ConvertAll(CloneGuardedAlternative));

      } else if (stmt is WhileStmt) {
        var s = (WhileStmt)stmt;
        r = new WhileStmt(Tok(s.Tok), CloneExpr(s.Guard), s.Invariants.ConvertAll(CloneMayBeFreeExpr), CloneSpecExpr(s.Decreases), CloneSpecFrameExpr(s.Mod), CloneBlockStmt(s.Body));

      } else if (stmt is AlternativeLoopStmt) {
        var s = (AlternativeLoopStmt)stmt;
        r = new AlternativeLoopStmt(Tok(s.Tok), s.Invariants.ConvertAll(CloneMayBeFreeExpr), CloneSpecExpr(s.Decreases), CloneSpecFrameExpr(s.Mod), s.Alternatives.ConvertAll(CloneGuardedAlternative));

      } else if (stmt is ForallStmt) {
        var s = (ForallStmt)stmt;
        r = new ForallStmt(Tok(s.Tok), s.BoundVars.ConvertAll(CloneBoundVar), null, CloneExpr(s.Range), s.Ens.ConvertAll(CloneMayBeFreeExpr), CloneStmt(s.Body));

      } else if (stmt is CalcStmt) {
          var s = (CalcStmt)stmt;
          r = new CalcStmt(Tok(s.Tok), s.Op, s.Lines.ConvertAll(CloneExpr), s.Hints.ConvertAll(CloneBlockStmt), new List<Nullable<BinaryExpr.Opcode>>(s.CustomOps));

      } else if (stmt is MatchStmt) {
        var s = (MatchStmt)stmt;
        r = new MatchStmt(Tok(s.Tok), CloneExpr(s.Source),
          s.Cases.ConvertAll(c => new MatchCaseStmt(Tok(c.tok), c.Id, c.Arguments.ConvertAll(CloneBoundVar), c.Body.ConvertAll(CloneStmt))));

      } else if (stmt is AssignSuchThatStmt) {
        var s = (AssignSuchThatStmt)stmt;
        r = new AssignSuchThatStmt(Tok(s.Tok), s.Lhss.ConvertAll(CloneExpr), CloneExpr(s.Expr), s.AssumeToken == null ? null : Tok(s.AssumeToken));

      } else if (stmt is UpdateStmt) {
        var s = (UpdateStmt)stmt;
        r = new UpdateStmt(Tok(s.Tok), s.Lhss.ConvertAll(CloneExpr), s.Rhss.ConvertAll(CloneRHS), s.CanMutateKnownState);

      } else if (stmt is VarDeclStmt) {
        var s = (VarDeclStmt)stmt;
        r = new VarDeclStmt(Tok(s.Tok), s.Lhss.ConvertAll(c => (VarDecl)CloneStmt(c)), (ConcreteUpdateStatement)CloneStmt(s.Update));

      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected statement
      }

      // add labels to the cloned statement
      AddStmtLabels(r, stmt.Labels);
      r.Attributes = CloneAttributes(stmt.Attributes);

      return r;
    }

    public void AddStmtLabels(Statement s, LList<Label> node) {
      if (node != null) {
        AddStmtLabels(s, node.Next);
        if (node.Data.Name == null) {
          // this indicates an implicit-target break statement that has been resolved; don't add it
        } else {
          s.Labels = new LList<Label>(new Label(Tok(node.Data.Tok), node.Data.Name), s.Labels);
        }
      }
    }

    public GuardedAlternative CloneGuardedAlternative(GuardedAlternative alt) {
      return new GuardedAlternative(Tok(alt.Tok), CloneExpr(alt.Guard), alt.Body.ConvertAll(CloneStmt));
    }

    public Function CloneFunction(Function f) {
      var tps = f.TypeArgs.ConvertAll(CloneTypeParam);
      var formals = f.Formals.ConvertAll(CloneFormal);
      var req = f.Req.ConvertAll(CloneExpr);
      var reads = f.Reads.ConvertAll(CloneFrameExpr);
      var decreases = CloneSpecExpr(f.Decreases);
      var ens = f.Ens.ConvertAll(CloneExpr);
      var body = CloneExpr(f.Body);

      if (f is Predicate) {
        return new Predicate(Tok(f.tok), f.Name, f.IsStatic, f.IsGhost, tps, f.OpenParen, formals,
          req, reads, ens, decreases, body, Predicate.BodyOriginKind.OriginalOrInherited, CloneAttributes(f.Attributes), false);
      } else if (f is CoPredicate) {
        return new CoPredicate(Tok(f.tok), f.Name, f.IsStatic, tps, f.OpenParen, formals,
          req, reads, ens, body, CloneAttributes(f.Attributes), false);
      } else {
        return new Function(Tok(f.tok), f.Name, f.IsStatic, f.IsGhost, tps, f.OpenParen, formals, CloneType(f.ResultType),
          req, reads, ens, decreases, body, CloneAttributes(f.Attributes), false);
      }
    }

    public Method CloneMethod(Method m) {
      Contract.Requires(m != null);

      var tps = m.TypeArgs.ConvertAll(CloneTypeParam);
      var ins = m.Ins.ConvertAll(CloneFormal);
      var req = m.Req.ConvertAll(CloneMayBeFreeExpr);
      var mod = CloneSpecFrameExpr(m.Mod);
      var decreases = CloneSpecExpr(m.Decreases);

      var ens = m.Ens.ConvertAll(CloneMayBeFreeExpr);

      var body = CloneBlockStmt(m.Body);
      if (m is Constructor) {
        return new Constructor(Tok(m.tok), m.Name, tps, ins,
          req, mod, ens, decreases, body, CloneAttributes(m.Attributes), false);
      } else if (m is CoMethod) {
        return new CoMethod(Tok(m.tok), m.Name, m.IsStatic, tps, ins, m.Outs.ConvertAll(CloneFormal),
          req, mod, ens, decreases, body, CloneAttributes(m.Attributes), false);
      } else {
        return new Method(Tok(m.tok), m.Name, m.IsStatic, m.IsGhost, tps, ins, m.Outs.ConvertAll(CloneFormal),
          req, mod, ens, decreases, body, CloneAttributes(m.Attributes), false);
      }
    }
    public virtual IToken Tok(IToken tok) {
      return tok;
    }
  }

  /// <summary>
  /// The CoMethodPostconditionSubstituter clones the postcondition declared on a comethod, but replaces
  /// the calls and equalities in "coConclusions" with corresponding prefix versions.  The resulting
  /// expression is then appropriate to be a postcondition of the comethod's corresponding prefix method.
  /// It is assumed that the source expression has been resolved.  Note, the "k" given to the constructor
  /// is not cloned with each use; it is simply used as is.
  /// </summary>
  class CoMethodPostconditionSubstituter : Cloner
  {
    readonly ISet<Expression> coConclusions;
    readonly Expression k;
    public CoMethodPostconditionSubstituter(ISet<Expression> coConclusions, Expression k) {
      Contract.Requires(coConclusions != null);
      Contract.Requires(k != null);
      this.coConclusions = coConclusions;
      this.k = k;
    }
    public override Expression CloneExpr(Expression expr) {
      if (expr is ConcreteSyntaxExpression) {
        var e = (ConcreteSyntaxExpression)expr;
        return CloneExpr(e.Resolved);
      } else  if (expr is FunctionCallExpr) {
        var e = (FunctionCallExpr)expr;
        if (coConclusions.Contains(e)) {
          var receiver = CloneExpr(e.Receiver);
          var args = new List<Expression>();
          args.Add(k);
          foreach (var arg in e.Args) {
            args.Add(CloneExpr(arg));
          }
          return new FunctionCallExpr(Tok(e.tok), e.Name + "#", receiver, e.OpenParen, args);
        }
      } else if (expr is BinaryExpr) {
        var e = (BinaryExpr)expr;
        if ((e.ResolvedOp == BinaryExpr.ResolvedOpcode.EqCommon || e.ResolvedOp == BinaryExpr.ResolvedOpcode.NeqCommon) && coConclusions.Contains(e)) {
          var op = e.ResolvedOp == BinaryExpr.ResolvedOpcode.EqCommon ? TernaryExpr.Opcode.PrefixEqOp : TernaryExpr.Opcode.PrefixNeqOp;
          var A = CloneExpr(e.E0);
          var B = CloneExpr(e.E1);
          var teq = new TernaryExpr(Tok(e.tok), op, k, A, B);
          return teq;
        }
      }
      return base.CloneExpr(expr);
    }
  }

  /// <summary>
  /// The task of the CoMethodBodyCloner is to fill in the implicit _k-1 arguments in corecursive comethod calls.
  /// The source statement and the given "k" are assumed to have been resolved, and the resulting statement will also be resolved.
  /// </summary>
  class CoMethodBodyCloner : Cloner
  {
    readonly CoMethod context;
    readonly Expression k;
    public CoMethodBodyCloner(CoMethod context, Expression k) {
      Contract.Requires(context != null);
      Contract.Requires(k != null);
      this.context = context;
      this.k = k;
    }
    public override Statement CloneStmt(Statement stmt) {
      if (stmt is UpdateStmt) {
        var s = (UpdateStmt)stmt;
        if (s.ResolvedStatements.Count == 1 && s.ResolvedStatements[0] is CallStmt) {
          var call = (CallStmt)s.ResolvedStatements[0];
          var moduleCaller = context.EnclosingClass.Module;
          var moduleCallee = call.Method.EnclosingClass.Module;
          if (call.Method is CoMethod && moduleCaller == moduleCallee && moduleCaller.CallGraph.GetSCCRepresentative(context) == moduleCaller.CallGraph.GetSCCRepresentative(call.Method)) {
            // we're looking at a recursive call to a comethod
            var args = new List<Expression>();
            args.Add(k);
            foreach (var arg in call.Args) {
              args.Add(CloneExpr(arg));
            }
            var rhs = new CallRhs(Tok(call.Tok), CloneExpr(call.Receiver), call.MethodName + "#", args);
            var r = new UpdateStmt(Tok(s.Tok), s.Lhss.ConvertAll(CloneExpr), new List<AssignmentRhs>() { rhs }, s.CanMutateKnownState);
            // don't forget to add labels to the cloned statement
            AddStmtLabels(r, stmt.Labels);
            r.Attributes = CloneAttributes(stmt.Attributes);
            return r;
          }
        }
      } else if (stmt is CallStmt) {
        var s = (CallStmt)stmt;
        if (s.Method is CoMethod) {
          var moduleCaller = context.EnclosingClass.Module;
          var moduleCallee = s.Method.EnclosingClass.Module;
          if (s.Method is CoMethod && moduleCaller == moduleCallee && moduleCaller.CallGraph.GetSCCRepresentative(context) == moduleCaller.CallGraph.GetSCCRepresentative(s.Method)) {
            // we're looking at a recursive call to a comethod
            var args = new List<Expression>();
            args.Add(k);
            foreach (var arg in s.Args) {
              args.Add(CloneExpr(arg));
            }
            var r = new CallStmt(Tok(s.Tok), s.Lhs.ConvertAll(CloneExpr), CloneExpr(s.Receiver), s.MethodName + "#", args);
            // don't forget to add labels to the cloned statement
            AddStmtLabels(r, stmt.Labels);
            r.Attributes = CloneAttributes(stmt.Attributes);
            return r;
          }
        }
      }
      return base.CloneStmt(stmt);
    }
  }
}
