
using System;
using System.Collections.Generic;
using System.Numerics;
using System.Diagnostics.Contracts;
using IToken = Microsoft.Boogie.IToken;

namespace Microsoft.Dafny
{
  class Cloner
  {
    public Cloner() {
    }
     
    public ModuleDefinition CloneModuleDefinition(ModuleDefinition m, string name) {
      ModuleDefinition nw;
      if (m is DefaultModuleDecl) {
        nw = new DefaultModuleDecl();
      } else {
        nw = new ModuleDefinition(Tok(m.tok), name, m.IsAbstract, m.IsFacade, m.IsExclusiveRefinement, m.RefinementBaseName, m.Module, CloneAttributes(m.Attributes), true);
      }
      foreach (var d in m.TopLevelDecls) {
        nw.TopLevelDecls.Add(CloneDeclaration(d, nw));
      }
      if (null != m.RefinementBase) {
        nw.RefinementBase = m.RefinementBase;
      }
      if (null != m.RefinementBaseSig) {
        nw.RefinementBaseSig = m.RefinementBaseSig;
      }
      nw.ClonedFrom = m;
      nw.Height = m.Height;
      return nw;
    }

    public TopLevelDecl CloneDeclaration(TopLevelDecl d, ModuleDefinition m) {
      Contract.Requires(d != null);
      Contract.Requires(m != null);

      if (d is OpaqueTypeDecl) {
        var dd = (OpaqueTypeDecl)d;
        return new OpaqueTypeDecl(Tok(dd.tok), dd.Name, m, dd.EqualitySupport, dd.TypeArgs.ConvertAll(CloneTypeParam), CloneAttributes(dd.Attributes), d);
      } else if (d is TypeSynonymDecl) {
        var dd = (TypeSynonymDecl)d;
        var tps = dd.TypeArgs.ConvertAll(CloneTypeParam);
        return new TypeSynonymDecl(Tok(dd.tok), dd.Name, tps, m, CloneType(dd.Rhs), CloneAttributes(dd.Attributes), dd);
      } else if (d is NewtypeDecl) {
        var dd = (NewtypeDecl)d;
        if (dd.Var == null) {
          return new NewtypeDecl(Tok(dd.tok), dd.Name, m, CloneType(dd.BaseType), CloneAttributes(dd.Attributes), dd);
        } else {
          return new NewtypeDecl(Tok(dd.tok), dd.Name, m, CloneBoundVar(dd.Var), CloneExpr(dd.Constraint), CloneAttributes(dd.Attributes), dd);
        }
      } else if (d is TupleTypeDecl) {
        var dd = (TupleTypeDecl)d;
        return new TupleTypeDecl(dd.Dims, dd.Module);
      } else if (d is IndDatatypeDecl) {
        var dd = (IndDatatypeDecl)d;
        var tps = dd.TypeArgs.ConvertAll(CloneTypeParam);
        var ctors = dd.Ctors.ConvertAll(CloneCtor);
        var dt = new IndDatatypeDecl(Tok(dd.tok), dd.Name, m, tps, ctors, CloneAttributes(dd.Attributes), dd);
        return dt;
      } else if (d is CoDatatypeDecl) {
        var dd = (CoDatatypeDecl)d;
        var tps = dd.TypeArgs.ConvertAll(CloneTypeParam);
        var ctors = dd.Ctors.ConvertAll(CloneCtor);
        var dt = new CoDatatypeDecl(Tok(dd.tok), dd.Name, m, tps, ctors, CloneAttributes(dd.Attributes), dd);
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
          body, CloneAttributes(dd.Attributes), dd.SignatureEllipsis);
        return iter;
      }
      else if (d is TraitDecl)
      {
          if (d is DefaultClassDecl)
          {
              var dd = (TraitDecl)d;
              var tps = dd.TypeArgs.ConvertAll(CloneTypeParam);
              var mm = dd.Members.ConvertAll(CloneMember);
              var cl = new DefaultClassDecl(m, mm);
              return cl;
          }
          else
          {
              var dd = (TraitDecl)d;
              var tps = dd.TypeArgs.ConvertAll(CloneTypeParam);
              var mm = dd.Members.ConvertAll(CloneMember);
              var cl = new TraitDecl(Tok(dd.tok), dd.Name, m, tps, mm, CloneAttributes(dd.Attributes), dd);
              return cl;
          }
      }
      else if (d is ClassDecl) {
        var dd = (ClassDecl)d;
        var tps = dd.TypeArgs.ConvertAll(CloneTypeParam);
        var mm = dd.Members.ConvertAll(CloneMember);
        if (d is DefaultClassDecl) {
          return new DefaultClassDecl(m, mm, ((DefaultClassDecl)d));
        } else {
          return new ClassDecl(Tok(dd.tok), dd.Name, m, tps, mm, CloneAttributes(dd.Attributes), dd.TraitsTyp.ConvertAll(CloneType), dd);
        }
      } else if (d is ModuleDecl) {
        if (d is LiteralModuleDecl) {
          var l = new LiteralModuleDecl(((LiteralModuleDecl)d).ModuleDef, m);
          l.Signature = ((ModuleDecl)d).Signature;
          return l;
        } else if (d is AliasModuleDecl) {
          var a = (AliasModuleDecl)d;
          var alias = new AliasModuleDecl(a.Path, a.tok, m, a.Opened);
          alias.Signature = a.Signature;
          return alias;
        } else if (d is ModuleFacadeDecl) {
          var a = (ModuleFacadeDecl)d;
          var abs = new ModuleFacadeDecl(a.Path, a.tok, m, a.CompilePath, a.Opened);
          abs.Signature = a.Signature;
          abs.OriginalSignature = a.OriginalSignature;
          return abs;
        } else if (d is ModuleExportDecl) {
          var a = (ModuleExportDecl)d;
          var export = new ModuleExportDecl(a.tok, m, a.Exports, a.Extends);
          export.Signature = a.Signature;
          return export;
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
      return new DatatypeCtor(Tok(ct.tok), ct.Name, ct.Formals.ConvertAll(CloneFormal), CloneAttributes(ct.Attributes), ct);
    }

    public TypeParameter CloneTypeParam(TypeParameter tp) {
      return new TypeParameter(Tok(tp.tok), tp.Name, tp.EqualitySupport, tp);
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

    public virtual Type CloneType(Type t) {
      if (t is BasicType) {
        return t;
      } else if (t is SetType) {
        var tt = (SetType)t;
        return new SetType(tt.Finite, CloneType(tt.Arg));
      } else if (t is SeqType) {
        var tt = (SeqType)t;
        return new SeqType(CloneType(tt.Arg));
      } else if (t is MultiSetType) {
        var tt = (MultiSetType)t;
        return new MultiSetType(CloneType(tt.Arg));
      } else if (t is MapType) {
        var tt = (MapType)t;
        return new MapType(tt.Finite, CloneType(tt.Domain), CloneType(tt.Range));
      } else if (t is ArrowType) {
        var tt = (ArrowType)t;
        return new ArrowType(Tok(tt.tok), tt.Args.ConvertAll(CloneType), CloneType(tt.Result));
      } else if (t is UserDefinedType) {
        var tt = (UserDefinedType)t;
#if TEST_TYPE_SYNONYM_TRANSPARENCY
        if (tt.Name == "type#synonym#transparency#test") {
          // time to drop the synonym wrapper
          var syn = (TypeSynonymDecl)tt.ResolvedClass;
          return CloneType(syn.Rhs);
        }
#endif
        return new UserDefinedType(Tok(tt.tok), CloneExpr(tt.NamePath));
      } else if (t is InferredTypeProxy) {
        return new InferredTypeProxy();
      } else if (t is OperationTypeProxy) {
        var p = (OperationTypeProxy)t;
        return new OperationTypeProxy(p.AllowInts, p.AllowReals, p.AllowChar, p.AllowSeq, p.AllowSetVarieties, p.AllowISet);
      } else if (t is ParamTypeProxy) {
        return new ParamTypeProxy(CloneTypeParam(((ParamTypeProxy)t).orig));
      } else {
        Contract.Assert(false);  // unexpected type (e.g., no other type proxies are expected at this time)
        return null;  // to please compiler
      }
    }

    public Formal CloneFormal(Formal formal) {
      Formal f = new Formal(Tok(formal.tok), formal.Name, CloneType(formal.Type), formal.InParam, formal.IsGhost);
      //if (f.Type is UserDefinedType && formal.Type is UserDefinedType)
      //    ((UserDefinedType)f.Type).ResolvedClass = ((UserDefinedType)(formal.Type)).ResolvedClass;
      return f;
    }

    public virtual BoundVar CloneBoundVar(BoundVar bv) {
      var bvNew = new BoundVar(Tok(bv.tok), bv.Name, CloneType(bv.SyntacticType));
      bvNew.IsGhost = bv.IsGhost;
      return bvNew;
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
      } else if (attrs.Name.StartsWith("_")) {
        // skip this attribute, since it would have been produced during resolution
        return CloneAttributes(attrs.Prev);
      } else if (attrs is UserSuppliedAttributes) {
        var usa = (UserSuppliedAttributes)attrs;
        return new UserSuppliedAttributes(Tok(usa.tok), Tok(usa.OpenBrace), Tok(usa.Colon), Tok(usa.CloseBrace), attrs.Args.ConvertAll(CloneExpr), CloneAttributes(attrs.Prev));
      } else {
        return new Attributes(attrs.Name, attrs.Args.ConvertAll(CloneExpr), CloneAttributes(attrs.Prev));
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
        if (e is StaticReceiverExpr) {
          var ee = (StaticReceiverExpr)e;
          return new StaticReceiverExpr(e.tok, CloneType(ee.UnresolvedType), ee.IsImplicit);
        } else if (e.Value == null) {          
          return new LiteralExpr(Tok(e.tok));
        } else if (e.Value is bool) {
          return new LiteralExpr(Tok(e.tok), (bool)e.Value);
        } else if (e is CharLiteralExpr) {
          return new CharLiteralExpr(Tok(e.tok), (string)e.Value);
        } else if (e is StringLiteralExpr) {
          var str = (StringLiteralExpr)e;
          return new StringLiteralExpr(Tok(e.tok), (string)e.Value, str.IsVerbatim);
        } else if (e.Value is Basetypes.BigDec) {
          return new LiteralExpr(Tok(e.tok), (Basetypes.BigDec)e.Value);
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
          return new SetDisplayExpr(Tok(e.tok), ((SetDisplayExpr)expr).Finite, e.Elements.ConvertAll(CloneExpr));
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
        return new MapDisplayExpr(Tok(expr.tok), e.Finite, pp);

      } else if (expr is NameSegment) {
        return CloneNameSegment(expr);
      } else if (expr is ExprDotName) {
        var e = (ExprDotName)expr;
        return new ExprDotName(Tok(e.tok), CloneExpr(e.Lhs), e.SuffixName, e.OptTypeArguments == null ? null : e.OptTypeArguments.ConvertAll(CloneType));
      } else if (expr is ApplySuffix) {
        var e = (ApplySuffix) expr;
        return CloneApplySuffix(e);
      } else if (expr is MemberSelectExpr) {
        var e = (MemberSelectExpr)expr;
        return new MemberSelectExpr(Tok(e.tok), CloneExpr(e.Obj), e.MemberName);

      } else if (expr is SeqSelectExpr) {
        var e = (SeqSelectExpr)expr;
        return new SeqSelectExpr(Tok(e.tok), e.SelectOne, CloneExpr(e.Seq), CloneExpr(e.E0), CloneExpr(e.E1));

      } else if (expr is MultiSelectExpr) {
        var e = (MultiSelectExpr)expr;
        return new MultiSelectExpr(Tok(e.tok), CloneExpr(e.Array), e.Indices.ConvertAll(CloneExpr));

      } else if (expr is SeqUpdateExpr) {
        var e = (SeqUpdateExpr)expr;
        return new SeqUpdateExpr(Tok(e.tok), CloneExpr(e.Seq), CloneExpr(e.Index), CloneExpr(e.Value));

      } else if (expr is DatatypeUpdateExpr) {
        var e = (DatatypeUpdateExpr)expr;
        return new DatatypeUpdateExpr(Tok(e.tok), CloneExpr(e.Root), e.Updates.ConvertAll(t => Tuple.Create(Tok(t.Item1), t.Item2, CloneExpr(t.Item3))));

      } else if (expr is FunctionCallExpr) {
        var e = (FunctionCallExpr)expr;
        return new FunctionCallExpr(Tok(e.tok), e.Name, CloneExpr(e.Receiver), e.OpenParen == null ? null : Tok(e.OpenParen), e.Args.ConvertAll(CloneExpr));

      } else if (expr is ApplyExpr) {
        var e = (ApplyExpr)expr;
        return new ApplyExpr(Tok(e.tok), CloneExpr(e.Function), e.Args.ConvertAll(CloneExpr));

      } else if (expr is OldExpr) {
        var e = (OldExpr)expr;
        return new OldExpr(Tok(e.tok), CloneExpr(e.E));

      } else if (expr is MultiSetFormingExpr) {
        var e = (MultiSetFormingExpr)expr;
        return new MultiSetFormingExpr(Tok(e.tok), CloneExpr(e.E));

      } else if (expr is UnaryOpExpr) {
        var e = (UnaryOpExpr)expr;
        return new UnaryOpExpr(Tok(e.tok), e.Op, CloneExpr(e.E));

      } else if (expr is ConversionExpr) {
        var e = (ConversionExpr)expr;
        return new ConversionExpr(Tok(e.tok), CloneExpr(e.E), CloneType(e.ToType));

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
        return new LetExpr(Tok(e.tok), e.LHSs.ConvertAll(CloneCasePattern), e.RHSs.ConvertAll(CloneExpr), CloneExpr(e.Body), e.Exact, e.Attributes);

      } else if (expr is NamedExpr) {
        var e = (NamedExpr)expr;
        return new NamedExpr(Tok(e.tok), e.Name, CloneExpr(e.Body));
      } else if (expr is ComprehensionExpr) {
        var e = (ComprehensionExpr)expr;
        var tk = Tok(e.tok);
        var bvs = e.BoundVars.ConvertAll(CloneBoundVar);
        var range = CloneExpr(e.Range);
        var term = CloneExpr(e.Term);
        if (e is QuantifierExpr) {
          var q = (QuantifierExpr)e;
          var tvs = q.TypeArgs.ConvertAll(CloneTypeParam);
          if (e is ForallExpr) {
            return new ForallExpr(tk, tvs, bvs, range, term, CloneAttributes(e.Attributes));
          } else if (e is ExistsExpr) {
            return new ExistsExpr(tk, tvs, bvs, range, term, CloneAttributes(e.Attributes));
          } else {
            Contract.Assert(false); throw new cce.UnreachableException();  // unexpected quantifier expression
          }
        } else if (e is MapComprehension) {
          return new MapComprehension(tk, ((MapComprehension)e).Finite, bvs, range, term, CloneAttributes(e.Attributes));
        } else if (e is LambdaExpr) {
          var l = (LambdaExpr)e;
          return new LambdaExpr(tk, l.OneShot, bvs, range, l.Reads.ConvertAll(CloneFrameExpr), term);
        } else {
          Contract.Assert(e is SetComprehension);
          var tt = (SetComprehension)e;
          return new SetComprehension(tk, tt.Finite, bvs, range, tt.TermIsImplicit ? null : term, CloneAttributes(e.Attributes));
        }

      } else if (expr is WildcardExpr) {
        return new WildcardExpr(Tok(expr.tok));

      } else if (expr is StmtExpr) {
        var e = (StmtExpr)expr;
        return new StmtExpr(Tok(e.tok), CloneStmt(e.S), CloneExpr(e.E));

      } else if (expr is ITEExpr) {
        var e = (ITEExpr)expr;
        return new ITEExpr(Tok(e.tok), e.IsExistentialGuard, CloneExpr(e.Test), CloneExpr(e.Thn), CloneExpr(e.Els));

      } else if (expr is AutoGeneratedExpression) {
        var e = (AutoGeneratedExpression)expr;
        var a = CloneExpr(e.E);
        return new AutoGeneratedExpression(Tok(e.tok), a);

      } else if (expr is ParensExpression) {
        var e = (ParensExpression)expr;
        return CloneExpr(e.E);  // skip the parentheses in the clone

      } else if (expr is MatchExpr) {
        var e = (MatchExpr)expr;
        return new MatchExpr(Tok(e.tok), CloneExpr(e.Source),
          e.Cases.ConvertAll(CloneMatchCaseExpr), e.UsesOptionalBraces);

      } else if (expr is NegationExpression) {
        var e = (NegationExpression)expr;
        return new NegationExpression(Tok(e.tok), CloneExpr(e.E));

      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected expression
      }
    }

    public MatchCaseExpr CloneMatchCaseExpr(MatchCaseExpr c) {
      Contract.Requires(c != null);
      if (c.Arguments != null) {
        Contract.Assert(c.CasePatterns == null);
        return new MatchCaseExpr(Tok(c.tok), c.Id, c.Arguments.ConvertAll(CloneBoundVar), CloneExpr(c.Body));
      } else {
        Contract.Assert(c.Arguments == null);
        Contract.Assert(c.CasePatterns != null);
        return new MatchCaseExpr(Tok(c.tok), c.Id, c.CasePatterns.ConvertAll(CloneCasePattern), CloneExpr(c.Body));
      }
    }

    public virtual Expression CloneApplySuffix(ApplySuffix e) {
        return new ApplySuffix(Tok(e.tok), CloneExpr(e.Lhs), e.Args.ConvertAll(CloneExpr));
    }

    public virtual CasePattern CloneCasePattern(CasePattern pat) {
      Contract.Requires(pat != null);
      if (pat.Var != null) {
        return new CasePattern(pat.tok, CloneBoundVar(pat.Var));
      } else if (pat.Arguments == null) {
        return new CasePattern(pat.tok, pat.Id, null);
      } else {
        return new CasePattern(pat.tok, pat.Id, pat.Arguments.ConvertAll(CloneCasePattern));
      }
    }

    public virtual NameSegment CloneNameSegment(Expression expr) {
      var e = (NameSegment)expr;
      return new NameSegment(Tok(e.tok), e.Name, e.OptTypeArguments == null ? null : e.OptTypeArguments.ConvertAll(CloneType));
    }

    public virtual AssignmentRhs CloneRHS(AssignmentRhs rhs) {
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
          c = new TypeRhs(Tok(r.Tok), CloneType(r.Path), r.Arguments.ConvertAll(CloneExpr), false);
        }
      }
      c.Attributes = CloneAttributes(rhs.Attributes);
      return c;
    }

    public virtual BlockStmt CloneBlockStmt(BlockStmt stmt) {
      if (stmt == null) {
        return null;
      } else {
        return new BlockStmt(Tok(stmt.Tok), Tok(stmt.EndTok), stmt.Body.ConvertAll(CloneStmt));
      }
    }

    public virtual Statement CloneStmt(Statement stmt) {
      if (stmt == null) {
        return null;
      }

      Statement r;
      if (stmt is AssertStmt) {
        var s = (AssertStmt)stmt;
        r = new AssertStmt(Tok(s.Tok), Tok(s.EndTok), CloneExpr(s.Expr), null);

      } else if (stmt is AssumeStmt) {
        var s = (AssumeStmt)stmt;
        r = new AssumeStmt(Tok(s.Tok), Tok(s.EndTok), CloneExpr(s.Expr), null);

      } else if (stmt is PrintStmt) {
        var s = (PrintStmt)stmt;
        r = new PrintStmt(Tok(s.Tok), Tok(s.EndTok), s.Args.ConvertAll(CloneExpr));

      } else if (stmt is BreakStmt) {
        var s = (BreakStmt)stmt;
        if (s.TargetLabel != null) {
          r = new BreakStmt(Tok(s.Tok), Tok(s.EndTok), s.TargetLabel);
        } else {
          r = new BreakStmt(Tok(s.Tok), Tok(s.EndTok), s.BreakCount);
        }

      } else if (stmt is ReturnStmt) {
        var s = (ReturnStmt)stmt;
        r = new ReturnStmt(Tok(s.Tok), Tok(s.EndTok), s.rhss == null ? null : s.rhss.ConvertAll(CloneRHS));

      } else if (stmt is YieldStmt) {
        var s = (YieldStmt)stmt;
        r = new YieldStmt(Tok(s.Tok), Tok(s.EndTok), s.rhss == null ? null : s.rhss.ConvertAll(CloneRHS));

      } else if (stmt is AssignStmt) {
        var s = (AssignStmt)stmt;
        r = new AssignStmt(Tok(s.Tok), Tok(s.EndTok), CloneExpr(s.Lhs), CloneRHS(s.Rhs));

      } else if (stmt is BlockStmt) {
        r = CloneBlockStmt((BlockStmt)stmt);

      } else if (stmt is IfStmt) {
        var s = (IfStmt)stmt;
        r = new IfStmt(Tok(s.Tok), Tok(s.EndTok), s.IsExistentialGuard, CloneExpr(s.Guard), CloneBlockStmt(s.Thn), CloneStmt(s.Els));

      } else if (stmt is AlternativeStmt) {
        var s = (AlternativeStmt)stmt;
        r = new AlternativeStmt(Tok(s.Tok), Tok(s.EndTok), s.Alternatives.ConvertAll(CloneGuardedAlternative));

      } else if (stmt is WhileStmt) {
        var s = (WhileStmt)stmt;
        r = new WhileStmt(Tok(s.Tok), Tok(s.EndTok), CloneExpr(s.Guard), s.Invariants.ConvertAll(CloneMayBeFreeExpr), CloneSpecExpr(s.Decreases), CloneSpecFrameExpr(s.Mod), CloneBlockStmt(s.Body));

      } else if (stmt is AlternativeLoopStmt) {
        var s = (AlternativeLoopStmt)stmt;
        r = new AlternativeLoopStmt(Tok(s.Tok), Tok(s.EndTok), s.Invariants.ConvertAll(CloneMayBeFreeExpr), CloneSpecExpr(s.Decreases), CloneSpecFrameExpr(s.Mod), s.Alternatives.ConvertAll(CloneGuardedAlternative));

      } else if (stmt is ForallStmt) {
        var s = (ForallStmt)stmt;
        r = new ForallStmt(Tok(s.Tok), Tok(s.EndTok), s.BoundVars.ConvertAll(CloneBoundVar), null, CloneExpr(s.Range), s.Ens.ConvertAll(CloneMayBeFreeExpr), CloneStmt(s.Body));
        if (s.ForallExpressions != null) {
          ((ForallStmt)r).ForallExpressions = s.ForallExpressions.ConvertAll(CloneExpr);
        }
      } else if (stmt is CalcStmt) {
        var s = (CalcStmt)stmt;
        // calc statements have the unusual property that the last line is duplicated.  If that is the case (which
        // we expect it to be here), we share the clone of that line as well.
        var lineCount = s.Lines.Count;
        var lines = new List<Expression>(lineCount);
        for (int i = 0; i < lineCount; i++) {
          lines.Add(i == lineCount - 1 && 2 <= lineCount && s.Lines[i] == s.Lines[i - 1] ? lines[i - 1] : CloneExpr(s.Lines[i]));
        }
        Contract.Assert(lines.Count == lineCount);
        r = new CalcStmt(Tok(s.Tok), Tok(s.EndTok), CloneCalcOp(s.Op), lines, s.Hints.ConvertAll(CloneBlockStmt), s.StepOps.ConvertAll(CloneCalcOp), CloneCalcOp(s.ResultOp), CloneAttributes(s.Attributes));

      } else if (stmt is MatchStmt) {
        var s = (MatchStmt)stmt;
        r = new MatchStmt(Tok(s.Tok), Tok(s.EndTok), CloneExpr(s.Source),
        s.Cases.ConvertAll(CloneMatchCaseStmt), s.UsesOptionalBraces);

      } else if (stmt is AssignSuchThatStmt) {
        var s = (AssignSuchThatStmt)stmt;
        r = new AssignSuchThatStmt(Tok(s.Tok), Tok(s.EndTok), s.Lhss.ConvertAll(CloneExpr), CloneExpr(s.Expr), s.AssumeToken == null ? null : Tok(s.AssumeToken), null);

      } else if (stmt is UpdateStmt) {
        var s = (UpdateStmt)stmt;
        r = new UpdateStmt(Tok(s.Tok), Tok(s.EndTok), s.Lhss.ConvertAll(CloneExpr), s.Rhss.ConvertAll(CloneRHS), s.CanMutateKnownState);

      } else if (stmt is VarDeclStmt) {
        var s = (VarDeclStmt)stmt;
        var lhss = s.Locals.ConvertAll(c => new LocalVariable(Tok(c.Tok), Tok(c.EndTok), c.Name, CloneType(c.OptionalType), c.IsGhost));
        r = new VarDeclStmt(Tok(s.Tok), Tok(s.EndTok), lhss, (ConcreteUpdateStatement)CloneStmt(s.Update));

      } else if (stmt is LetStmt) {
        var s = (LetStmt) stmt;
        r = new LetStmt(Tok(s.Tok), Tok(s.EndTok), s.LHSs.ConvertAll(CloneCasePattern), s.RHSs.ConvertAll(CloneExpr));

      } else if (stmt is ModifyStmt) {
        var s = (ModifyStmt)stmt;
        var mod = CloneSpecFrameExpr(s.Mod);
        var body = s.Body == null ? null : CloneBlockStmt(s.Body);
        r = new ModifyStmt(Tok(s.Tok), Tok(s.EndTok), mod.Expressions, mod.Attributes, body);

      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected statement
      }

      // add labels to the cloned statement
      AddStmtLabels(r, stmt.Labels);
      r.Attributes = CloneAttributes(stmt.Attributes);

      return r;
    }

    public MatchCaseStmt CloneMatchCaseStmt(MatchCaseStmt c) {
      Contract.Requires(c != null);
      if (c.Arguments != null) {
        Contract.Assert(c.CasePatterns == null);
        return new MatchCaseStmt(Tok(c.tok), c.Id, c.Arguments.ConvertAll(CloneBoundVar), c.Body.ConvertAll(CloneStmt));
      } else {
        Contract.Assert(c.Arguments == null);
        Contract.Assert(c.CasePatterns != null);
        return new MatchCaseStmt(Tok(c.tok), c.Id, c.CasePatterns.ConvertAll(CloneCasePattern), c.Body.ConvertAll(CloneStmt));
      }
    }

    public CalcStmt.CalcOp CloneCalcOp(CalcStmt.CalcOp op) {
      if (op is CalcStmt.BinaryCalcOp) {
        return new CalcStmt.BinaryCalcOp(((CalcStmt.BinaryCalcOp) op).Op);
      } else if (op is CalcStmt.TernaryCalcOp) {
        return new CalcStmt.TernaryCalcOp(CloneExpr(((CalcStmt.TernaryCalcOp) op).Index));
      } else {
        Contract.Assert(false);
        throw new cce.UnreachableException();
      }
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
      return new GuardedAlternative(Tok(alt.Tok), alt.IsExistentialGuard, CloneExpr(alt.Guard), alt.Body.ConvertAll(CloneStmt));
    }

    public Function CloneFunction(Function f, string newName = null) {
      var tps = f.TypeArgs.ConvertAll(CloneTypeParam);
      var formals = f.Formals.ConvertAll(CloneFormal);
      var req = f.Req.ConvertAll(CloneExpr);
      var reads = f.Reads.ConvertAll(CloneFrameExpr);
      var decreases = CloneSpecExpr(f.Decreases);
      var ens = f.Ens.ConvertAll(CloneExpr);
      var body = CloneExpr(f.Body);

      if (newName == null) {
        newName = f.Name;
      }

      if (f is Predicate) {
        return new Predicate(Tok(f.tok), newName, f.HasStaticKeyword, f.IsProtected, f.IsGhost, tps, formals,
          req, reads, ens, decreases, body, Predicate.BodyOriginKind.OriginalOrInherited, CloneAttributes(f.Attributes), null, f);
      } else if (f is InductivePredicate) {
        return new InductivePredicate(Tok(f.tok), newName, f.HasStaticKeyword, f.IsProtected, tps, formals,
          req, reads, ens, body, CloneAttributes(f.Attributes), null, f);
      } else if (f is CoPredicate) {
        return new CoPredicate(Tok(f.tok), newName, f.HasStaticKeyword, f.IsProtected, tps, formals,
          req, reads, ens, body, CloneAttributes(f.Attributes), null, f);
      } else {
        return new Function(Tok(f.tok), newName, f.HasStaticKeyword, f.IsProtected, f.IsGhost, tps, formals, CloneType(f.ResultType),
          req, reads, ens, decreases, body, CloneAttributes(f.Attributes), null, f);
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
          req, mod, ens, decreases, body, CloneAttributes(m.Attributes), null, m);
      } else if (m is InductiveLemma) {
        return new InductiveLemma(Tok(m.tok), m.Name, m.HasStaticKeyword, tps, ins, m.Outs.ConvertAll(CloneFormal),
          req, mod, ens, decreases, body, CloneAttributes(m.Attributes), null, m);
      } else if (m is CoLemma) {
        return new CoLemma(Tok(m.tok), m.Name, m.HasStaticKeyword, tps, ins, m.Outs.ConvertAll(CloneFormal),
          req, mod, ens, decreases, body, CloneAttributes(m.Attributes), null, m);
      } else if (m is Lemma) {
        return new Lemma(Tok(m.tok), m.Name, m.HasStaticKeyword, tps, ins, m.Outs.ConvertAll(CloneFormal),
          req, mod, ens, decreases, body, CloneAttributes(m.Attributes), null, m);
      } else {
        return new Method(Tok(m.tok), m.Name, m.HasStaticKeyword, m.IsGhost, tps, ins, m.Outs.ConvertAll(CloneFormal),
          req, mod, ens, decreases, body, CloneAttributes(m.Attributes), null, m);
      }
    }
    public virtual IToken Tok(IToken tok) {
      return tok;
    }
  }

  class ClonerButDropMethodBodies : Cloner
  {
    public ClonerButDropMethodBodies()
      : base() {
    }

    public override BlockStmt CloneBlockStmt(BlockStmt stmt) {
      return null;
    }
  }

  /// <summary>
  /// Subclass of Cloner that collects some common functionality between FixpointLemmaSpecificationSubstituter and
  /// FixpointLemmaBodyCloner.
  /// </summary>
  abstract class FixpointCloner : Cloner
  {
    protected readonly Expression k;
    protected readonly ErrorReporter reporter;
    protected readonly string suffix;
    protected FixpointCloner(Expression k, ErrorReporter reporter)
    {
      Contract.Requires(k != null);
      Contract.Requires(reporter != null);
      this.k = k;
      this.reporter = reporter;
      this.suffix = string.Format("#[{0}]", Printer.ExprToString(k));
    }
    protected Expression CloneCallAndAddK(FunctionCallExpr e) {
      Contract.Requires(e != null);
      var receiver = CloneExpr(e.Receiver);
      var args = new List<Expression>();
      args.Add(k);
      foreach (var arg in e.Args) {
        args.Add(CloneExpr(arg));
      }
      var fexp = new FunctionCallExpr(Tok(e.tok), e.Name + "#", receiver, e.OpenParen, args);
      reporter.Info(MessageSource.Cloner, e.tok, e.Name + suffix);
      return fexp;
    }
  }

  /// <summary>
  /// The FixpointLemmaSpecificationSubstituter clones the precondition (or postcondition) declared
  /// on an inductive lemma (resp. colemma), but replaces the calls and equalities in "coConclusions"
  /// with corresponding prefix versions.  The resulting expression is then appropriate to be a
  /// precondition (resp. postcondition) of the inductive lemma's (resp. colemma's) corresponding prefix lemma.
  /// It is assumed that the source expression has been resolved.  Note, the "k" given to the constructor
  /// is not cloned with each use; it is simply used as is.
  /// The resulting expression needs to be resolved by the caller.
  /// </summary>
  class FixpointLemmaSpecificationSubstituter : FixpointCloner
  {
    readonly bool isCoContext;
    readonly ISet<Expression> friendlyCalls;
    public FixpointLemmaSpecificationSubstituter(ISet<Expression> friendlyCalls, Expression k, ErrorReporter reporter, bool isCoContext)
      : base(k, reporter)
    {
      Contract.Requires(friendlyCalls != null);
      Contract.Requires(k != null);
      Contract.Requires(reporter != null);
      this.isCoContext = isCoContext;
      this.friendlyCalls = friendlyCalls;
    }
    public override Expression CloneExpr(Expression expr) {
      if (expr is ConcreteSyntaxExpression) {
        var e = (ConcreteSyntaxExpression)expr;
        // Note, the CoLemmaPostconditionSubstituter is an unusual cloner in that it operates on
        // resolved expressions.  Hence, we bypass the syntactic parts here.
        return CloneExpr(e.Resolved);
      } else if (expr is FunctionCallExpr) {
        var e = (FunctionCallExpr)expr;
        if (friendlyCalls.Contains(e)) {
          return CloneCallAndAddK(e);
        }
      } else if (expr is BinaryExpr && isCoContext) {
        var e = (BinaryExpr)expr;
        if ((e.ResolvedOp == BinaryExpr.ResolvedOpcode.EqCommon || e.ResolvedOp == BinaryExpr.ResolvedOpcode.NeqCommon) && friendlyCalls.Contains(e)) {
          var op = e.ResolvedOp == BinaryExpr.ResolvedOpcode.EqCommon ? TernaryExpr.Opcode.PrefixEqOp : TernaryExpr.Opcode.PrefixNeqOp;
          var A = CloneExpr(e.E0);
          var B = CloneExpr(e.E1);
          var teq = new TernaryExpr(Tok(e.tok), op, k, A, B);
          var opString = op == TernaryExpr.Opcode.PrefixEqOp ? "==" : "!=";
          reporter.Info(MessageSource.Cloner, e.tok, opString + suffix);
          return teq;
        }
      }
      return base.CloneExpr(expr);
    }
    public override Type CloneType(Type t) {
      if (t is UserDefinedType) {
        var tt = (UserDefinedType)t;
        // We want syntactic cloning of the Expression that is tt.NamePath, unlike the semantic (that is, post-resolved)
        // cloning that CloneExpr is doing above.
        return new UserDefinedType(Tok(tt.tok), CloneNamePathExpression(tt.NamePath));
      } else {
        return base.CloneType(t);
      }
    }
    Expression CloneNamePathExpression(Expression expr) {
      Contract.Requires(expr is NameSegment || expr is ExprDotName);
      if (expr is NameSegment) {
        var e = (NameSegment)expr;
        return new NameSegment(Tok(e.tok), e.Name, e.OptTypeArguments == null ? null : e.OptTypeArguments.ConvertAll(CloneType));
      } else {
        var e = (ExprDotName)expr;
        return new ExprDotName(Tok(e.tok), CloneNamePathExpression(e.Lhs), e.SuffixName, e.OptTypeArguments == null ? null : e.OptTypeArguments.ConvertAll(CloneType));
      }
    }
  }

  /// <summary>
  /// The task of the FixpointLemmaBodyCloner is to fill in the implicit _k-1 arguments in recursive inductive/co-lemma calls
  /// and in calls to the focal predicates.
  /// The source statement and the given "k" are assumed to have been resolved.
  /// </summary>
  class FixpointLemmaBodyCloner : FixpointCloner
  {
    readonly FixpointLemma context;
    readonly ISet<FixpointPredicate> focalPredicates;
    public FixpointLemmaBodyCloner(FixpointLemma context, Expression k, ISet<FixpointPredicate> focalPredicates, ErrorReporter reporter)
      : base(k, reporter)
    {
      Contract.Requires(context != null);
      Contract.Requires(k != null);
      Contract.Requires(reporter != null);
      this.context = context;
      this.focalPredicates = focalPredicates;
    }
    public override Expression CloneExpr(Expression expr) {
      if (DafnyOptions.O.RewriteFocalPredicates) {
        if (expr is FunctionCallExpr) {
          var e = (FunctionCallExpr)expr;
#if DEBUG_PRINT
          if (e.Function.Name.EndsWith("#") && Contract.Exists(focalPredicates, p => e.Function.Name == p.Name + "#")) {
            Console.WriteLine("{0}({1},{2}): DEBUG: Possible opportunity to rely on new rewrite: {3}", e.tok.filename, e.tok.line, e.tok.col, Printer.ExprToString(e));
          }
#endif
          // Note, we don't actually ever get here, because all calls will have been parsed as ApplySuffix.
          // However, if something changes in the future (for example, some rewrite that changing an ApplySuffix
          // to its resolved FunctionCallExpr), then we do want this code, so with the hope of preventing
          // some error in the future, this case is included.  (Of course, it is currently completely untested!)
          var f = e.Function as FixpointPredicate;
          if (f != null && focalPredicates.Contains(f)) {
#if DEBUG_PRINT
            var r = CloneCallAndAddK(e);
            Console.WriteLine("{0}({1},{2}): DEBUG: Rewrote extreme predicate into prefix predicate: {3}", e.tok.filename, e.tok.line, e.tok.col, Printer.ExprToString(r));
            return r;
#else
            return CloneCallAndAddK(e);
#endif
          }
        } else if (expr is ApplySuffix) {
          var apply = (ApplySuffix)expr;
          if (!apply.WasResolved()) {
            // Since we're assuming the enclosing statement to have been resolved, this ApplySuffix must
            // be part of an ExprRhs that actually designates a method call.  Such an ApplySuffix does
            // not get listed as being resolved, but its components (like its .Lhs) are resolved.
            var mse = (MemberSelectExpr)apply.Lhs.Resolved;
            Contract.Assume(mse.Member is Method);
          } else {
            var fce = apply.Resolved as FunctionCallExpr;
            if (fce != null) {
#if DEBUG_PRINT
              if (fce.Function.Name.EndsWith("#") && Contract.Exists(focalPredicates, p => fce.Function.Name == p.Name + "#")) {
                Console.WriteLine("{0}({1},{2}): DEBUG: Possible opportunity to rely on new rewrite: {3}", fce.tok.filename, fce.tok.line, fce.tok.col, Printer.ExprToString(fce));
              }
#endif
              var f = fce.Function as FixpointPredicate;
              if (f != null && focalPredicates.Contains(f)) {
#if DEBUG_PRINT
                var r = CloneCallAndAddK(fce);
                Console.WriteLine("{0}({1},{2}): DEBUG: Rewrote extreme predicate into prefix predicate: {3}", fce.tok.filename, fce.tok.line, fce.tok.col, Printer.ExprToString(r));
                return r;
#else
                return CloneCallAndAddK(fce);
#endif
              }
            }
          }
        }
      }
      return base.CloneExpr(expr);
    }
    public override AssignmentRhs CloneRHS(AssignmentRhs rhs) {
      var r = rhs as ExprRhs;
      if (r != null && r.Expr is ApplySuffix) {
        var apply = (ApplySuffix)r.Expr;
        var mse = apply.Lhs.Resolved as MemberSelectExpr;
        if (mse != null && mse.Member is FixpointLemma && ModuleDefinition.InSameSCC(context, (FixpointLemma)mse.Member)) {
          // we're looking at a recursive call to a fixpoint lemma
          Contract.Assert(apply.Lhs is NameSegment || apply.Lhs is ExprDotName);  // this is the only way a call statement can have been parsed
          // clone "apply.Lhs", changing the inductive/co lemma to the prefix lemma; then clone "apply", adding in the extra argument
          Expression lhsClone;
          if (apply.Lhs is NameSegment) {
            var lhs = (NameSegment)apply.Lhs;
            lhsClone = new NameSegment(Tok(lhs.tok), lhs.Name + "#", lhs.OptTypeArguments == null ? null : lhs.OptTypeArguments.ConvertAll(CloneType));
          } else {
            var lhs = (ExprDotName)apply.Lhs;
            lhsClone = new ExprDotName(Tok(lhs.tok), CloneExpr(lhs.Lhs), lhs.SuffixName + "#", lhs.OptTypeArguments == null ? null : lhs.OptTypeArguments.ConvertAll(CloneType));
          }
          var args = new List<Expression>();
          args.Add(k);
          apply.Args.ForEach(arg => args.Add(CloneExpr(arg)));
          var applyClone = new ApplySuffix(Tok(apply.tok), lhsClone, args);
          var c = new ExprRhs(applyClone);
          reporter.Info(MessageSource.Cloner, apply.Lhs.tok, mse.Member.Name + suffix);
          return c;
        }
      }
      return base.CloneRHS(rhs);
    }
  }


  class ResolvedCloner : Cloner {

    public override Type CloneType(Type t) {
      Type new_t = base.CloneType(t);

      if (t is UserDefinedType) {
        var tt = (UserDefinedType)t;
        var new_tt = (UserDefinedType)new_t;

        new_tt.ResolvedClass = tt.ResolvedClass;
        new_tt.ResolvedParam = tt.ResolvedParam;                
      }

      return new_t;
    }

    public override CasePattern CloneCasePattern(CasePattern pat) {
      if (pat.Var != null) {
        var newPat = new CasePattern(pat.tok, CloneBoundVar(pat.Var));
        newPat.AssembleExpr(null);
        return newPat;
      } else {
        var newArgs = pat.Arguments == null ? null : pat.Arguments.ConvertAll(CloneCasePattern);
        var patE = (DatatypeValue)pat.Expr;
        var newPat = new CasePattern(pat.tok, pat.Id, newArgs);
        newPat.Ctor = pat.Ctor;
        newPat.AssembleExpr(patE.InferredTypeArgs.ConvertAll(CloneType));
        return newPat;
      }
    }

    public override BoundVar CloneBoundVar(BoundVar bv) {
      // The difference here from the overridden method is that we do CloneType(bv.Type) instead of CloneType(bv.SyntacticType)
      var bvNew = new BoundVar(Tok(bv.tok), bv.Name, CloneType(bv.Type));
      bvNew.IsGhost = bv.IsGhost;
      return bvNew;
    }
  }

}
