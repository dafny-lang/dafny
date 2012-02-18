//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
// This file contains the transformations that are applied to a module that is
// constructed as a refinement of another.  It is invoked during program resolution,
// so the transformation is done syntactically.  Upon return from the RefinementTransformer,
// the caller is expected to resolve the resulting module.
//
// As for now (and perhaps this is always the right thing to do), attributes do
// not survive the transformation.
//-----------------------------------------------------------------------------

using System;
using System.Collections.Generic;
using System.Numerics;
using System.Diagnostics.Contracts;
using IToken = Microsoft.Boogie.IToken;

namespace Microsoft.Dafny {
  public class RefinementToken : TokenWrapper
  {
    public readonly ModuleDecl InheritingModule;
    public RefinementToken(IToken tok, ModuleDecl m)
      : base(tok)
    {
      Contract.Requires(tok != null);
      Contract.Requires(m != null);
      this.InheritingModule = m;
    }

    public static bool IsInherited(IToken tok, ModuleDecl m) {
      while (tok is NestedToken) {
        var n = (NestedToken)tok;
        // check Outer
        var r = n.Outer as RefinementToken;
        if (r == null || r.InheritingModule != m) {
          return false;
        }
        // continue to check Inner
        tok = n.Inner;
      }
      var rtok = tok as RefinementToken;
      return rtok != null && rtok.InheritingModule == m;
    }
    public override string filename {
      get { return WrappedToken.filename + "[" + InheritingModule.Name + "]"; }
      set { throw new NotSupportedException(); }
    }
  }

  public class RefinementTransformer
  {
    ResolutionErrorReporter reporter;
    public RefinementTransformer(ResolutionErrorReporter reporter) {
      Contract.Requires(reporter != null);
      this.reporter = reporter;
    }

    private ModuleDecl moduleUnderConstruction;  // non-null for the duration of Construct calls

    public void Construct(ModuleDecl m) {
      Contract.Requires(m != null);
      Contract.Requires(m.RefinementBase != null);

      Contract.Assert(moduleUnderConstruction == null);
      moduleUnderConstruction = m;
      var prev = m.RefinementBase;

      // Include the imports of the base.  Note, prev is itself NOT added as an import
      // of m; instead, the contents from prev is merged directly into m.
      // (Here, we change the import declarations.  But edges for these imports will
      // not be added to the importGraph of the calling resolver.  However, the refines
      // clause gave rise to an edge in the importGraph, so the transitive import edges
      // are represented in the importGraph.)
      foreach (var im in prev.Imports) {
        if (!m.ImportNames.Contains(im.Name)) {
          m.ImportNames.Add(im.Name);
          m.Imports.Add(im);
        }
      }

      // Create a simple name-to-decl dictionary.  Ignore any duplicates at this time.
      var declaredNames = new Dictionary<string, int>();
      for (int i = 0; i < m.TopLevelDecls.Count; i++) {
        var d = m.TopLevelDecls[i];
        if (!declaredNames.ContainsKey(d.Name)) {
          declaredNames.Add(d.Name, i);
        }
      }

      // Merge the declarations of prev into the declarations of m

      foreach (var d in prev.TopLevelDecls) {
        int index;
        if (!declaredNames.TryGetValue(d.Name, out index)) {
          m.TopLevelDecls.Add(CloneDeclaration(d, m));
        } else {
          var nw = m.TopLevelDecls[index];
          if (d is ArbitraryTypeDecl) {
            // this is allowed to be refined by any type declaration, so just keep the new one
          } else if (nw is ArbitraryTypeDecl) {
            reporter.Error(nw, "an arbitrary type declaration ({0}) in a refining module cannot replace a more specific type declaration in the refinement base", nw.Name);
          } else if (nw is DatatypeDecl) {
            reporter.Error(nw, "a datatype declaration ({0}) in a refinement module can only replace an arbitrary-type declaration", nw.Name);
          } else {
            Contract.Assert(nw is ClassDecl);
            if (d is DatatypeDecl) {
              reporter.Error(nw, "a class declaration ({0}) in a refining module cannot replace a datatype declaration in the refinement base", nw.Name);
            } else {
              m.TopLevelDecls[index] = MergeClass((ClassDecl)nw, (ClassDecl)d);
            }
          }
        }
      }

      Contract.Assert(moduleUnderConstruction == m);
      moduleUnderConstruction = null;
    }

    IToken Tok(IToken tok) {
      if (moduleUnderConstruction == null) {
        return tok;
      } else {
        return new RefinementToken(tok, moduleUnderConstruction);
      }
    }

    // -------------------------------------------------- Cloning ---------------------------------------------------------------

    TopLevelDecl CloneDeclaration(TopLevelDecl d, ModuleDecl m) {
      Contract.Requires(d != null);
      Contract.Requires(m != null);

      if (d is ArbitraryTypeDecl) {
        var dd = (ArbitraryTypeDecl)d;
        return new ArbitraryTypeDecl(Tok(dd.tok), dd.Name, m, null);
      } else if (d is DatatypeDecl) {
        var dd = (DatatypeDecl)d;
        var tps = dd.TypeArgs.ConvertAll(CloneTypeParam);
        var ctors = dd.Ctors.ConvertAll(CloneCtor);
        var dt = new DatatypeDecl(Tok(dd.tok), dd.Name, m, tps, ctors, null);
        return dt;
      } else if (d is ClassDecl) {
        var dd = (ClassDecl)d;
        var tps = dd.TypeArgs.ConvertAll(CloneTypeParam);
        var mm = dd.Members.ConvertAll(CloneMember);
        var cl = new ClassDecl(Tok(dd.tok), dd.Name, m, tps, mm, null);
        return cl;
      } else {
        Contract.Assert(false);  // unexpected declaration
        return null;  // to please compiler
      }
    }

    DatatypeCtor CloneCtor(DatatypeCtor ct) {
      return new DatatypeCtor(Tok(ct.tok), ct.Name, ct.Formals.ConvertAll(CloneFormal), null);
    }

    TypeParameter CloneTypeParam(TypeParameter tp) {
      return new TypeParameter(Tok(tp.tok), tp.Name);
    }

    MemberDecl CloneMember(MemberDecl member) {
      if (member is Field) {
        var f = (Field)member;
        return new Field(Tok(f.tok), f.Name, f.IsGhost, f.IsMutable, CloneType(f.Type), null);
      } else if (member is Function) {
        var f = (Function)member;
        return CloneFunction(Tok(f.tok), f, f.IsGhost, null, null, null);
      } else {
        var m = (Method)member;
        return CloneMethod(m, null, null);
      }
    }

    Type CloneType(Type t) {
      if (t is BasicType) {
        return t;
      } else if (t is SetType) {
        var tt = (SetType)t;
        return new SetType(tt.Arg);
      } else if (t is SeqType) {
        var tt = (SeqType)t;
        return new SeqType(tt.Arg);
      } else if (t is MultiSetType) {
        var tt = (MultiSetType)t;
        return new MultiSetType(tt.Arg);
      } else if (t is UserDefinedType) {
        var tt = (UserDefinedType)t;
        return new UserDefinedType(Tok(tt.tok), tt.Name, tt.TypeArgs.ConvertAll(CloneType));
      } else if (t is InferredTypeProxy) {
        return new InferredTypeProxy();
      } else {
        Contract.Assert(false);  // unexpected type (e.g., no other type proxies are expected at this time)
        return null;  // to please compiler
      }
    }

    Formal CloneFormal(Formal formal) {
      return new Formal(Tok(formal.tok), formal.Name, CloneType(formal.Type), formal.InParam, formal.IsGhost);
    }

    BoundVar CloneBoundVar(BoundVar bv) {
      return new BoundVar(Tok(bv.tok), bv.Name, CloneType(bv.Type));
    }

    Specification<Expression> CloneSpecExpr(Specification<Expression> spec) {
      var ee = spec.Expressions == null ? null : spec.Expressions.ConvertAll(CloneExpr);
      return new Specification<Expression>(ee, null);
    }

    Specification<FrameExpression> CloneSpecFrameExpr(Specification<FrameExpression> frame) {
      var ee = frame.Expressions == null ? null : frame.Expressions.ConvertAll(CloneFrameExpr);
      return new Specification<FrameExpression>(ee, null);
    }

    FrameExpression CloneFrameExpr(FrameExpression frame) {
      return new FrameExpression(CloneExpr(frame.E), frame.FieldName);
    }

    Attributes.Argument CloneAttrArg(Attributes.Argument aa) {
      if (aa.E != null) {
        return new Attributes.Argument(Tok(aa.Tok), CloneExpr(aa.E));
      } else {
        return new Attributes.Argument(Tok(aa.Tok), aa.S);
      }
    }

    MaybeFreeExpression CloneMayBeFreeExpr(MaybeFreeExpression expr) {
      return new MaybeFreeExpression(CloneExpr(expr.E), expr.IsFree);
    }

    Expression CloneExpr(Expression expr) {
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

      } else if (expr is AllocatedExpr) {
        var e = (AllocatedExpr)expr;
        return new AllocatedExpr(Tok(e.tok), CloneExpr(e.E));

      } else if (expr is UnaryExpr) {
        var e = (UnaryExpr)expr;
        return new UnaryExpr(Tok(e.tok), e.Op, CloneExpr(e.E));

      } else if (expr is BinaryExpr) {
        var e = (BinaryExpr)expr;
        return new BinaryExpr(Tok(e.tok), e.Op, CloneExpr(e.E0), CloneExpr(e.E1));

      } else if (expr is ChainingExpression) {
        var e = (ChainingExpression)expr;
        return CloneExpr(e.E);  // just clone the desugaring, since it's already available

      } else if (expr is LetExpr) {
        var e = (LetExpr)expr;
        return new LetExpr(Tok(e.tok), e.Vars.ConvertAll(CloneBoundVar), e.RHSs.ConvertAll(CloneExpr), CloneExpr(e.Body));

      } else if (expr is ComprehensionExpr) {
        var e = (ComprehensionExpr)expr;
        var tk = Tok(e.tok);
        var bvs = e.BoundVars.ConvertAll(CloneBoundVar);
        var range = CloneExpr(e.Range);
        var term = CloneExpr(e.Term);
        if (e is ForallExpr) {
          return new ForallExpr(tk, bvs, range, term, null);
        } else if (e is ExistsExpr) {
          return new ExistsExpr(tk, bvs, range, term, null);
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

      } else if (expr is ITEExpr) {
        var e = (ITEExpr)expr;
        return new ITEExpr(Tok(e.tok), CloneExpr(e.Test), CloneExpr(e.Thn), CloneExpr(e.Els));

      } else if (expr is ParensExpression) {
        var e = (ParensExpression)expr;
        return CloneExpr(e.E);  // skip the parentheses in the clone

      } else if (expr is IdentifierSequence) {
        var e = (IdentifierSequence)expr;
        var aa = e.Arguments == null ? null : e.Arguments.ConvertAll(CloneExpr);
        return new IdentifierSequence(e.Tokens.ConvertAll(tk => Tok(tk)), e.OpenParen == null ? null : Tok(e.OpenParen), aa);

      } else if (expr is MatchExpr) {
        var e = (MatchExpr)expr;
        return new MatchExpr(Tok(e.tok), CloneExpr(e.Source),
          e.Cases.ConvertAll(c => new MatchCaseExpr(Tok(c.tok), c.Id, c.Arguments.ConvertAll(CloneBoundVar), CloneExpr(c.Body))));

      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected expression
      }
    }

    AssignmentRhs CloneRHS(AssignmentRhs rhs) {
      if (rhs is ExprRhs) {
        var r = (ExprRhs)rhs;
        return new ExprRhs(CloneExpr(r.Expr));
      } else if (rhs is HavocRhs) {
        return new HavocRhs(Tok(rhs.Tok));
      } else {
        var r = (TypeRhs)rhs;
        if (r.ArrayDimensions != null) {
          return new TypeRhs(Tok(r.Tok), CloneType(r.EType), r.ArrayDimensions.ConvertAll(CloneExpr));
        } else if (r.InitCall != null) {
          return new TypeRhs(Tok(r.Tok), CloneType(r.EType), (CallStmt)CloneStmt(r.InitCall));
        } else {
          return new TypeRhs(Tok(r.Tok), CloneType(r.EType));
        }
      }
    }

    BlockStmt CloneBlockStmt(BlockStmt stmt) {
      if (stmt == null) {
        return null;
      } else {
        return new BlockStmt(Tok(stmt.Tok), stmt.Body.ConvertAll(CloneStmt));
      }
    }

    Statement CloneStmt(Statement stmt) {
      if (stmt == null) {
        return null;
      }

      Statement r;
      if (stmt is AssertStmt) {
        var s = (AssertStmt)stmt;
        r = new AssertStmt(Tok(s.Tok), CloneExpr(s.Expr));

      } else if (stmt is AssumeStmt) {
        var s = (AssumeStmt)stmt;
        r = new AssumeStmt(Tok(s.Tok), CloneExpr(s.Expr));

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
        r = new IfStmt(Tok(s.Tok), CloneExpr(s.Guard), CloneStmt(s.Thn), CloneStmt(s.Els));

      } else if (stmt is AlternativeStmt) {
        var s = (AlternativeStmt)stmt;
        r = new AlternativeStmt(Tok(s.Tok), s.Alternatives.ConvertAll(CloneGuardedAlternative));

      } else if (stmt is WhileStmt) {
        var s = (WhileStmt)stmt;
        r = new WhileStmt(Tok(s.Tok), CloneExpr(s.Guard), s.Invariants.ConvertAll(CloneMayBeFreeExpr), CloneSpecExpr(s.Decreases), CloneSpecFrameExpr(s.Mod), CloneStmt(s.Body));

      } else if (stmt is AlternativeLoopStmt) {
        var s = (AlternativeLoopStmt)stmt;
        r = new AlternativeLoopStmt(Tok(s.Tok), s.Invariants.ConvertAll(CloneMayBeFreeExpr), CloneSpecExpr(s.Decreases), CloneSpecFrameExpr(s.Mod), s.Alternatives.ConvertAll(CloneGuardedAlternative));

      } else if (stmt is ParallelStmt) {
        var s = (ParallelStmt)stmt;
        r = new ParallelStmt(Tok(s.Tok), s.BoundVars.ConvertAll(CloneBoundVar), null, CloneExpr(s.Range), s.Ens.ConvertAll(CloneMayBeFreeExpr), CloneStmt(s.Body));

      } else if (stmt is MatchStmt) {
        var s = (MatchStmt)stmt;
        r = new MatchStmt(Tok(s.Tok), CloneExpr(s.Source),
          s.Cases.ConvertAll(c => new MatchCaseStmt(Tok(c.tok), c.Id, c.Arguments.ConvertAll(CloneBoundVar), c.Body.ConvertAll(CloneStmt))));

      } else if (stmt is UpdateStmt) {
        var s = (UpdateStmt)stmt;
        r = new UpdateStmt(Tok(s.Tok), s.Lhss.ConvertAll(CloneExpr), s.Rhss.ConvertAll(CloneRHS), s.CanMutateKnownState);

      } else if (stmt is VarDeclStmt) {
        var s = (VarDeclStmt)stmt;
        r = new VarDeclStmt(Tok(s.Tok), s.Lhss.ConvertAll(c => (VarDecl)CloneStmt(c)), (UpdateStmt)CloneStmt(s.Update));

      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected statement
      }

      // add labels to the cloned statement
      AddStmtLabels(r, stmt.Labels);

      return r;
    }

    void AddStmtLabels(Statement s, LabelNode node) {
      if (node != null) {
        AddStmtLabels(s, node.Next);
        s.Labels = new LabelNode(Tok(node.Tok), node.Label, s.Labels);
      }
    }

    GuardedAlternative CloneGuardedAlternative(GuardedAlternative alt) {
      return new GuardedAlternative(Tok(alt.Tok), CloneExpr(alt.Guard), alt.Body.ConvertAll(CloneStmt));
    }

    Function CloneFunction(IToken tok, Function f, bool isGhost, List<Expression> moreEnsures, Expression moreBody, Expression replacementBody) {
      Contract.Requires(moreBody == null || f is Predicate);
      Contract.Requires(moreBody == null || replacementBody == null);

      var tps = f.TypeArgs.ConvertAll(CloneTypeParam);
      var formals = f.Formals.ConvertAll(CloneFormal);
      var req = f.Req.ConvertAll(CloneExpr);
      var reads = f.Reads.ConvertAll(CloneFrameExpr);
      var decreases = CloneSpecExpr(f.Decreases);

      var previousModuleUnderConstruction = moduleUnderConstruction;
      if (moreBody != null || replacementBody != null) { moduleUnderConstruction = null; }
      var ens = f.Ens.ConvertAll(CloneExpr);
      moduleUnderConstruction = previousModuleUnderConstruction;
      if (moreEnsures != null) {
        ens.AddRange(moreEnsures);
      }

      Expression body;
      if (replacementBody != null) {
        body = replacementBody;
      } else if (moreBody != null) {
        if (f.Body == null) {
          body = moreBody;
        } else {
          body = new BinaryExpr(f.tok, BinaryExpr.Opcode.And, CloneExpr(f.Body), moreBody);
        }
      } else {
        body = CloneExpr(f.Body);
      }

      if (f is Predicate) {
        return new Predicate(tok, f.Name, f.IsStatic, isGhost, f.IsUnlimited, tps, f.OpenParen, formals,
          req, reads, ens, decreases, body, moreBody != null, null, false);
      } else {
        return new Function(tok, f.Name, f.IsStatic, isGhost, f.IsUnlimited, tps, f.OpenParen, formals, CloneType(f.ResultType),
          req, reads, ens, decreases, body, null, false);
      }
    }

    Method CloneMethod(Method m, List<MaybeFreeExpression> moreEnsures, BlockStmt replacementBody) {
      Contract.Requires(m != null);

      var tps = m.TypeArgs.ConvertAll(CloneTypeParam);
      var ins = m.Ins.ConvertAll(CloneFormal);
      var req = m.Req.ConvertAll(CloneMayBeFreeExpr);
      var mod = CloneSpecFrameExpr(m.Mod);
      var decreases = CloneSpecExpr(m.Decreases);

      var previousModuleUnderConstruction = moduleUnderConstruction;
      if (replacementBody != null) { moduleUnderConstruction = null; }
      var ens = m.Ens.ConvertAll(CloneMayBeFreeExpr);
      if (replacementBody != null) { moduleUnderConstruction = previousModuleUnderConstruction; }
      if (moreEnsures != null) {
        ens.AddRange(moreEnsures);
      }

      var body = replacementBody ?? CloneBlockStmt(m.Body);
      if (m is Constructor) {
        return new Constructor(Tok(m.tok), m.Name, tps, ins,
          req, mod, ens, decreases, body, null, false);
      } else {
        return new Method(Tok(m.tok), m.Name, m.IsStatic, m.IsGhost, tps, ins, m.Outs.ConvertAll(CloneFormal),
          req, mod, ens, decreases, body, null, false);
      }
    }

    // -------------------------------------------------- Merging ---------------------------------------------------------------

    ClassDecl MergeClass(ClassDecl nw, ClassDecl prev) {
      // Create a simple name-to-member dictionary.  Ignore any duplicates at this time.
      var declaredNames = new Dictionary<string, int>();
      for (int i = 0; i < nw.Members.Count; i++) {
        var member = nw.Members[i];
        if (!declaredNames.ContainsKey(member.Name)) {
          declaredNames.Add(member.Name, i);
        }
      }

      // Merge the declarations of prev into the declarations of m
      foreach (var member in prev.Members) {
        int index;
        if (!declaredNames.TryGetValue(member.Name, out index)) {
          nw.Members.Add(CloneMember(member));
        } else {
          var nwMember = nw.Members[index];
          if (nwMember is Field) {
            reporter.Error(nwMember, "a field declaration ({0}) in a refining class ({1}) is not allowed replace an existing declaration in the refinement base", nwMember.Name, nw.Name);

          } else if (nwMember is Function) {
            var f = (Function)nwMember;
            bool isPredicate = f is Predicate;
            string s = isPredicate ? "predicate" : "function";
            if (!(member is Function) || isPredicate && !(member is Predicate)) {
              reporter.Error(nwMember, "a {0} declaration ({1}) can only refine a {0}", s, nwMember.Name);
            } else {
              var prevFunction = (Function)member;
              if (f.Req.Count != 0) {
                reporter.Error(f.Req[0].tok, "a refining {0} is not allowed to add preconditions", s);
              }
              if (f.Reads.Count != 0) {
                reporter.Error(f.Reads[0].E.tok, "a refining {0} is not allowed to extend the reads clause", s);
              }
              if (f.Decreases.Expressions.Count != 0) {
                reporter.Error(f.Decreases.Expressions[0].tok, "decreases clause on refining {0} not supported", s);
              }

              if (prevFunction.IsStatic != f.IsStatic) {
                reporter.Error(f, "a function in a refining module cannot be changed from static to non-static or vice versa: {0}", f.Name);
              }
              if (prevFunction.IsUnlimited != f.IsUnlimited) {
                reporter.Error(f, "a function in a refining module cannot be changed from unlimited to limited or vice versa: {0}", f.Name);
              }
              if (!prevFunction.IsGhost && f.IsGhost) {
                reporter.Error(f, "a function method cannot be changed into a (ghost) function in a refining module: {0}", f.Name);
              } else if (prevFunction.IsGhost && !f.IsGhost && prevFunction.Body != null) {
                reporter.Error(f, "a function can be changed into a function method in a refining module only if the function has not yet been given a body: {0}", f.Name);
              }
              if (f.SignatureIsOmitted) {
                Contract.Assert(f.TypeArgs.Count == 0);
                Contract.Assert(f.Formals.Count == 0);
              } else {
                CheckAgreement_TypeParameters(f.tok, prevFunction.TypeArgs, f.TypeArgs, f.Name, "function");
                CheckAgreement_Parameters(f.tok, prevFunction.Formals, f.Formals, f.Name, "function", "parameter");
                if (!TypesAreEqual(prevFunction.ResultType, f.ResultType)) {
                  reporter.Error(f, "the result type of function '{0}' ({1}) differs from the result type of the corresponding function in the module it refines ({2})", f.Name, f.ResultType, prevFunction.ResultType);
                }
              }

              Expression moreBody = null;
              Expression replacementBody = null;
              if (isPredicate) {
                moreBody = f.Body;
              } else if (prevFunction.Body == null) {
                replacementBody = f.Body;
              } else if (f.Body != null) {
                reporter.Error(nwMember, "a refining function is not allowed to extend/change the body");
              }
              nw.Members[index] = CloneFunction(f.tok, prevFunction, f.IsGhost, f.Ens, moreBody, replacementBody);
            }

          } else {
            var m = (Method)nwMember;
            if (!(member is Method)) {
              reporter.Error(nwMember, "a method declaration ({0}) can only refine a method", nwMember.Name);
            } else {
              var prevMethod = (Method)member;
              if (m.Req.Count != 0) {
                reporter.Error(m.Req[0].E.tok, "a refining method is not allowed to add preconditions");
              }
              if (m.Mod.Expressions.Count != 0) {
                reporter.Error(m.Mod.Expressions[0].E.tok, "a refining method is not allowed to extend the modifies clause");
              }
              if (m.Decreases.Expressions.Count != 0) {
                reporter.Error(m.Decreases.Expressions[0].tok, "decreases clause on refining method not supported");
              }

              if (prevMethod.IsStatic != m.IsStatic) {
                reporter.Error(m, "a method in a refining module cannot be changed from static to non-static or vice versa: {0}", m.Name);
              }
              if (prevMethod.IsGhost && !m.IsGhost) {
                reporter.Error(m, "a method cannot be changed into a ghost method in a refining module: {0}", m.Name);
              } else if (!prevMethod.IsGhost && m.IsGhost) {
                reporter.Error(m, "a ghost method cannot be changed into a non-ghost method in a refining module: {0}", m.Name);
              }
              if (m.SignatureIsOmitted) {
                Contract.Assert(m.TypeArgs.Count == 0);
                Contract.Assert(m.Ins.Count == 0);
                Contract.Assert(m.Outs.Count == 0);
              } else {
                CheckAgreement_TypeParameters(m.tok, prevMethod.TypeArgs, m.TypeArgs, m.Name, "method");
                CheckAgreement_Parameters(m.tok, prevMethod.Ins, m.Ins, m.Name, "method", "in-parameter");
                CheckAgreement_Parameters(m.tok, prevMethod.Outs, m.Outs, m.Name, "method", "out-parameter");
              }

              var replacementBody = m.Body;
              if (replacementBody != null) {
                if (prevMethod.Body == null) {
                  // cool
                } else {
                  replacementBody = MergeBlockStmt(replacementBody, prevMethod.Body);
                }
              }
              nw.Members[index] = CloneMethod(prevMethod, m.Ens, replacementBody);
            }
          }
        }
      }

      return nw;
    }

    void CheckAgreement_TypeParameters(IToken tok, List<TypeParameter> old, List<TypeParameter> nw, string name, string thing) {
      Contract.Requires(tok != null);
      Contract.Requires(old != null);
      Contract.Requires(nw != null);
      Contract.Requires(name != null);
      Contract.Requires(thing != null);
      if (old.Count != nw.Count) {
        reporter.Error(tok, "{0} '{1}' is declared with a different number of type parameters ({2} instead of {3}) than the corresponding {0} in the module it refines", thing, name, nw.Count, old.Count);
      } else {
        for (int i = 0; i < old.Count; i++) {
          var o = old[i];
          var n = nw[i];
          if (o.Name != n.Name) {
            reporter.Error(n.tok, "type parameters are not allowed to be renamed from the names given in the {0} in the module being refined (expected '{1}', found '{2}')", thing, o.Name, n.Name);
          }
        }
      }
    }

    void CheckAgreement_Parameters(IToken tok, List<Formal> old, List<Formal> nw, string name, string thing, string parameterKind) {
      Contract.Requires(tok != null);
      Contract.Requires(old != null);
      Contract.Requires(nw != null);
      Contract.Requires(name != null);
      Contract.Requires(thing != null);
      Contract.Requires(parameterKind != null);
      if (old.Count != nw.Count) {
        reporter.Error(tok, "{0} '{1}' is declared with a different number of {2} ({3} instead of {4}) than the corresponding {0} in the module it refines", thing, name, parameterKind, nw.Count, old.Count);
      } else {
        for (int i = 0; i < old.Count; i++) {
          var o = old[i];
          var n = nw[i];
          if (o.Name != n.Name) {
            reporter.Error(n.tok, "there is a difference in name of {0} {1} ('{2}' versus '{3}') of {4} {5} compared to corresponding {4} in the module it refines", parameterKind, i, n.Name, o.Name, thing, name);
          } else if (!o.IsGhost && n.IsGhost) {
            reporter.Error(n.tok, "{0} '{1}' of {2} {3} cannot be changed, compared to the corresponding {2} in the module it refines, from non-ghost to ghost", parameterKind, n.Name, thing, name);
          } else if (o.IsGhost && !n.IsGhost) {
            reporter.Error(n.tok, "{0} '{1}' of {2} {3} cannot be changed, compared to the corresponding {2} in the module it refines, from ghost to non-ghost", parameterKind, n.Name, thing, name);
          } else if (!TypesAreEqual(o.Type, n.Type)) {
            reporter.Error(n.tok, "the type of {0} '{1}' is different from the type of the same {0} in the corresponding {2} in the module it refines ('{3}' instead of '{4}')", parameterKind, n.Name, thing, n.Type, o.Type);
          }
        }
      }
    }

    bool TypesAreEqual(Type t, Type u) {
      Contract.Requires(t != null);
      Contract.Requires(u != null);
      return t.ToString() == u.ToString();
    }

    BlockStmt MergeBlockStmt(BlockStmt skeleton, BlockStmt oldStmt) {
      Contract.Requires(skeleton != null);
      Contract.Requires(oldStmt != null);

      var body = new List<Statement>();
      int i = 0, j = 0;
      while (i < skeleton.Body.Count) {
        var cur = skeleton.Body[i];
        if (j == oldStmt.Body.Count) {
          if (!(cur is SkeletonStatement)) {
            MergeAddStatement(cur, body);
          } else if (((SkeletonStatement)cur).S == null) {
            // the "..." matches the empty statement sequence
          } else {
            reporter.Error(cur.Tok, "skeleton statement does not match old statement");
          }
          i++;
        } else {
          var oldS = oldStmt.Body[j];
          /* See how the two statements match up.
           *   cur                         oldS                         result
           *   ------                      ------                       ------
           *   assert ...;                 assume E;                    assert E;
           *   assert ...;                 assert E;                    assert E;
           *   assert E;                                                assert E;
           *   
           *   var x:=E;                   var x;                       var x:=E;
           *   var VarProduction;                                       var VarProduction;
           *   
           *   if ... Then else Else       if (G) Then' else Else'      if (G) Merge(Then,Then') else Merge(Else,Else')
           *   if (G) Then else Else       if (*) Then' else Else'      if (G) Merge(Then,Then') else Merge(Else,Else')
           *
           *   while ... LoopSpec ...      while (G) LoopSpec' Body     while (G) Merge(LoopSpec,LoopSpec') Body
           *   while ... LoopSpec Body     while (G) LoopSpec' Body'    while (G) Merge(LoopSpec,LoopSpec') Merge(Body,Body')
           *   while (G) LoopSpec ...      while (*) LoopSpec' Body     while (G) Merge(LoopSpec,LoopSpec') Body
           *   while (G) LoopSpec Body     while (*) LoopSpec' Body'    while (G) Merge(LoopSpec,LoopSpec') Merge(Body,Body')
           *   
           *   ...; S                      StmtThatDoesNotMatchS; S'    StatementThatDoesNotMatchS; Merge( ...;S , S')
           * 
           * Note, LoopSpec must contain only invariant declarations (as the parser ensures for the first three cases).
           * Note, there is an implicit "...;" at the end of every block in a skeleton.
           *   
           * TODO:  should also handle labels and some form of new "replace" statement
           */
          if (cur is SkeletonStatement) {
            var ass = ((SkeletonStatement)cur).S as AssertStmt;
            if (ass != null) {
              Contract.Assert(((SkeletonStatement)cur).ConditionOmitted);
              var oldAssume = oldS as PredicateStmt;
              if (oldAssume == null) {
                reporter.Error(cur.Tok, "assert template does not match old statement");
              } else {
                body.Add(new AssertStmt(ass.Tok, CloneExpr(oldAssume.Expr)));
              }
              i++; j++;
            } else {
              reporter.Error(cur.Tok, "sorry, this skeleton statement is not yet supported");
              i++;
            }
          } else {
            var cNew = cur as VarDeclStmt;
            var cOld = oldS as VarDeclStmt;
            if (cNew != null && cOld != null && cNew.Lhss.Count == 1 && cOld.Lhss.Count == 1 &&
              cNew.Lhss[0].Name == cOld.Lhss[0].Name && cOld.Update == null) {
              body.Add(cNew);  // TODO:  there should perhaps be some more validity checks here first
              i++; j++;
            } else {
              MergeAddStatement(cur, body);
              i++;
            }
          }
        }
      }
      // implement the implicit "...;" at the end of each block statement skeleton
      for (; j < oldStmt.Body.Count; j++) {
        MergeAddStatement(CloneStmt(oldStmt.Body[j]), body);
      }
      return new BlockStmt(skeleton.Tok, body);
    }

    /// <summary>
    /// Add "s" to "stmtList", but complain if "s" contains further occurrences of "..." or if "s" assigns to a
    /// variable that was not declared in the refining module.
    /// TODO: and what about new control flow?
    /// </summary>
    void MergeAddStatement(Statement s, List<Statement> stmtList) {
      Contract.Requires(s != null);
      Contract.Requires(stmtList != null);
      if (s is AssertStmt) {
        // this is fine to add
      } else {
        // TODO: validity checks
      }
      stmtList.Add(s);
    }

    // ---------------------- additional methods -----------------------------------------------------------------------------

    public static bool ContainsChange(Expression expr, ModuleDecl m) {
      Contract.Requires(expr != null);
      Contract.Requires(m != null);

      if (expr is FunctionCallExpr) {
        var e = (FunctionCallExpr)expr;
        if (e.Function.EnclosingClass.Module == m) {
          var p = e.Function as Predicate;
          if (p != null && p.BodyIsExtended) {
            return true;
          }
        }
      }

      foreach (var ee in expr.SubExpressions) {
        if (ContainsChange(ee, m)) {
          return true;
        }
      }
      return false;
    }
  }
}
