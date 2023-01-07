// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

using System;
using System.Collections.Generic;
using System.Numerics;
using System.Diagnostics.Contracts;
using System.Linq;
using Microsoft.Boogie;

namespace Microsoft.Dafny {

  interface ICloneable<out T> {
    T Clone(Cloner cloner);
  }

  public class Cloner {
    public bool CloneResolvedFields { get; }
    private readonly Dictionary<Statement, Statement> statementClones = new();
    private readonly Dictionary<IVariable, IVariable> clones = new();
    private readonly Dictionary<MemberDecl, MemberDecl> memberClones = new();

    public void AddStatementClone(Statement original, Statement clone) {
      statementClones.Add(original, clone);
    }

    public Cloner(bool cloneResolvedFields = false) {
      this.CloneResolvedFields = cloneResolvedFields;
    }

    public virtual ModuleDefinition CloneModuleDefinition(ModuleDefinition m, string name) {
      ModuleDefinition nw;
      if (m is DefaultModuleDef) {
        nw = new DefaultModuleDef();
      } else {
        nw = new ModuleDefinition(Tok(m.tok), name, m.PrefixIds, m.IsAbstract, m.IsFacade,
          m.RefinementQId, m.EnclosingModule, CloneAttributes(m.Attributes),
          true, m.IsToBeVerified, m.IsToBeCompiled);
      }
      foreach (var d in m.TopLevelDecls) {
        nw.TopLevelDecls.Add(CloneDeclaration(d, nw));
      }
      foreach (var tup in m.PrefixNamedModules) {
        var newTup = new Tuple<List<IToken>, LiteralModuleDecl>(tup.Item1, (LiteralModuleDecl)CloneDeclaration(tup.Item2, nw));
        nw.PrefixNamedModules.Add(newTup);
      }
      nw.Height = m.Height;
      return nw;
    }

    public virtual TopLevelDecl CloneDeclaration(TopLevelDecl d, ModuleDefinition m) {
      Contract.Requires(d != null);
      Contract.Requires(m != null);

      if (d is OpaqueTypeDecl) {
        var dd = (OpaqueTypeDecl)d;
        return new OpaqueTypeDecl(Tok(dd.tok), dd.Name, m, CloneTPChar(dd.Characteristics), dd.TypeArgs.ConvertAll(CloneTypeParam), dd.Members.ConvertAll(d => CloneMember(d, false)), CloneAttributes(dd.Attributes), dd.IsRefining);
      } else if (d is SubsetTypeDecl) {
        Contract.Assume(!(d is NonNullTypeDecl));  // don't clone the non-null type declaration; close the class, which will create a new non-null type declaration
        var dd = (SubsetTypeDecl)d;
        var tps = dd.TypeArgs.ConvertAll(CloneTypeParam);
        return new SubsetTypeDecl(Tok(dd.tok), dd.Name, CloneTPChar(dd.Characteristics), tps, m, CloneBoundVar(dd.Var, false), CloneExpr(dd.Constraint), dd.WitnessKind, CloneExpr(dd.Witness), CloneAttributes(dd.Attributes));
      } else if (d is TypeSynonymDecl) {
        var dd = (TypeSynonymDecl)d;
        var tps = dd.TypeArgs.ConvertAll(CloneTypeParam);
        return new TypeSynonymDecl(Tok(dd.tok), dd.Name, CloneTPChar(dd.Characteristics), tps, m, CloneType(dd.Rhs), CloneAttributes(dd.Attributes));
      } else if (d is NewtypeDecl) {
        var dd = (NewtypeDecl)d;
        if (dd.Var == null) {
          return new NewtypeDecl(Tok(dd.tok), dd.Name, m, CloneType(dd.BaseType),
            dd.Members.ConvertAll(d => CloneMember(d, false)), CloneAttributes(dd.Attributes), dd.IsRefining);
        } else {
          return new NewtypeDecl(Tok(dd.tok), dd.Name, m, CloneBoundVar(dd.Var, false),
            CloneExpr(dd.Constraint), dd.WitnessKind, CloneExpr(dd.Witness),
            dd.Members.ConvertAll(d => CloneMember(d, false)), CloneAttributes(dd.Attributes), dd.IsRefining);
        }
      } else if (d is TupleTypeDecl) {
        // Tuple type declarations only exist in the system module. Therefore, they are never cloned.
        Contract.Assert(false);
        throw new cce.UnreachableException();
      } else if (d is IndDatatypeDecl) {
        var dd = (IndDatatypeDecl)d;
        var tps = dd.TypeArgs.ConvertAll(CloneTypeParam);
        var ctors = dd.Ctors.ConvertAll(CloneCtor);
        var dt = new IndDatatypeDecl(Tok(dd.tok), dd.Name, m, tps, ctors, dd.Members.ConvertAll(d => CloneMember(d, false)), CloneAttributes(dd.Attributes), dd.IsRefining);
        return dt;
      } else if (d is CoDatatypeDecl) {
        var dd = (CoDatatypeDecl)d;
        var tps = dd.TypeArgs.ConvertAll(CloneTypeParam);
        var ctors = dd.Ctors.ConvertAll(CloneCtor);
        var dt = new CoDatatypeDecl(Tok(dd.tok), dd.Name, m, tps, ctors, dd.Members.ConvertAll(d => CloneMember(d, false)), CloneAttributes(dd.Attributes), dd.IsRefining);
        return dt;
      } else if (d is IteratorDecl) {
        var dd = (IteratorDecl)d;
        var tps = dd.TypeArgs.ConvertAll(CloneTypeParam);
        var ins = dd.Ins.ConvertAll(bv => CloneFormal(bv, false));
        var outs = dd.Outs.ConvertAll(bv => CloneFormal(bv, false));
        var reads = CloneSpecFrameExpr(dd.Reads);
        var mod = CloneSpecFrameExpr(dd.Modifies);
        var decr = CloneSpecExpr(dd.Decreases);
        var req = dd.Requires.ConvertAll(CloneAttributedExpr);
        var yreq = dd.YieldRequires.ConvertAll(CloneAttributedExpr);
        var ens = dd.Ensures.ConvertAll(CloneAttributedExpr);
        var yens = dd.YieldEnsures.ConvertAll(CloneAttributedExpr);
        var body = CloneBlockStmt(dd.Body);
        var iter = new IteratorDecl(Tok(dd.tok), dd.Name, m,
          tps, ins, outs, reads, mod, decr,
          req, ens, yreq, yens,
          body, CloneAttributes(dd.Attributes), dd.SignatureEllipsis);
        return iter;
      } else if (d is TraitDecl) {
        var dd = (TraitDecl)d;
        var tps = dd.TypeArgs.ConvertAll(CloneTypeParam);
        var mm = dd.Members.ConvertAll(d => CloneMember(d, false));
        var cl = new TraitDecl(Tok(dd.tok), dd.Name, m, tps, mm, CloneAttributes(dd.Attributes), dd.IsRefining, dd.ParentTraits.ConvertAll(CloneType));
        return cl;
      } else if (d is ClassDecl) {
        var dd = (ClassDecl)d;
        var tps = dd.TypeArgs.ConvertAll(CloneTypeParam);
        var mm = dd.Members.ConvertAll(d => CloneMember(d, false));
        if (d is DefaultClassDecl) {
          return new DefaultClassDecl(m, mm);
        } else {
          return new ClassDecl(Tok(dd.tok), dd.Name, m, tps, mm, CloneAttributes(dd.Attributes), dd.IsRefining, dd.ParentTraits.ConvertAll(CloneType));
        }
      } else if (d is ModuleDecl) {
        if (d is LiteralModuleDecl moduleDecl) {
          return new LiteralModuleDecl(moduleDecl.ModuleDef, m) {
            DefaultExport = moduleDecl.DefaultExport
          };
        } else if (d is AliasModuleDecl) {
          var a = (AliasModuleDecl)d;
          return new AliasModuleDecl(a.TargetQId?.Clone(false), a.tok, m, a.Opened, a.Exports);
        } else if (d is AbstractModuleDecl) {
          var a = (AbstractModuleDecl)d;
          return new AbstractModuleDecl(a.QId?.Clone(false), a.tok, m, a.Opened, a.Exports);
        } else if (d is ModuleExportDecl) {
          var a = (ModuleExportDecl)d;
          return new ModuleExportDecl(a.tok, a.Name, m, a.Exports, a.Extends, a.ProvideAll, a.RevealAll, a.IsDefault, a.IsRefining);
        } else {
          Contract.Assert(false);  // unexpected declaration
          return null;  // to please compiler
        }
      } else {
        Contract.Assert(false);  // unexpected declaration
        return null;  // to please compiler
      }
    }

    public TypeParameter.TypeParameterCharacteristics CloneTPChar(TypeParameter.TypeParameterCharacteristics characteristics) {
      TypeParameter.EqualitySupportValue eqSupport;
      if (characteristics.EqualitySupport == TypeParameter.EqualitySupportValue.InferredRequired) {
        eqSupport = TypeParameter.EqualitySupportValue.Unspecified;
      } else {
        eqSupport = characteristics.EqualitySupport;
      }
      return new TypeParameter.TypeParameterCharacteristics(eqSupport, characteristics.AutoInit, characteristics.ContainsNoReferenceTypes);
    }

    public DatatypeCtor CloneCtor(DatatypeCtor ct) {
      return new DatatypeCtor(Tok(ct.tok), ct.Name, ct.IsGhost, ct.Formals.ConvertAll(bv => CloneFormal(bv, false)), CloneAttributes(ct.Attributes));
    }

    public TypeParameter CloneTypeParam(TypeParameter tp) {
      return new TypeParameter(Tok(tp.tok), tp.Name, tp.VarianceSyntax, CloneTPChar(tp.Characteristics));
    }

    public virtual MemberDecl CloneMember(MemberDecl member, bool isReference) {
      return memberClones.GetOrCreate(member, () => {
        if (isReference) {
          return member;
        }

        if (member is Field) {
          var f = (Field)member;
          return CloneField(f);
        } else if (member is Function) {
          var f = (Function)member;
          return CloneFunction(f);
        } else {
          var m = (Method)member;
          return CloneMethod(m);
        }
      });
    }

    public virtual Type CloneType(Type t) {
      if (t == null) {
        return null;
      }
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
        return new UserDefinedType(this, tt);
      } else if (t is InferredTypeProxy proxy) {
        var inferredTypeProxy = new InferredTypeProxy();
        if (CloneResolvedFields) {
          inferredTypeProxy.T = proxy.T;
        }
        return inferredTypeProxy;
      } else if (t is ParamTypeProxy) {
        return new ParamTypeProxy(CloneTypeParam(((ParamTypeProxy)t).orig));
      } else {
        Contract.Assert(false);  // unexpected type (e.g., no other type proxies are expected at this time)
        return null;  // to please compiler
      }
    }

    public virtual Formal CloneFormal(Formal formal, bool isReference) {
      return (Formal)clones.GetOrCreate(formal, () => isReference ? formal :
        new Formal(Tok(formal.tok), formal.Name, CloneType(formal.Type), formal.InParam, formal.IsGhost,
        CloneExpr(formal.DefaultValue), formal.IsOld, formal.IsNameOnly, formal.IsOlder, formal.NameForCompilation));
    }

    public virtual BoundVar CloneBoundVar(BoundVar bv, bool isReference) {
      return (BoundVar)clones.GetOrCreate(bv, () => {
        if (isReference) {
          return bv;
        }
        var bvNew = new BoundVar(Tok(bv.tok), bv.Name, CloneType(bv.SyntacticType));
        bvNew.IsGhost = bv.IsGhost;
        return bvNew;
      });
    }

    public virtual LocalVariable CloneLocalVariable(LocalVariable local, bool isReference) {
      return (LocalVariable)clones.GetOrCreate(local, () => isReference ? local : new LocalVariable(this, local));
    }
    public virtual VT CloneIVariable<VT>(VT v, bool isReference)
      where VT : class, IVariable {
      if (v == null) {
        return null;
      }

      var iv = (IVariable)v;
      if (iv is Formal formal) {
        iv = CloneFormal(formal, isReference);
      } else if (iv is BoundVar boundVar) {
        iv = CloneBoundVar(boundVar, isReference);
      } else if (iv is LocalVariable localVariable) {
        iv = CloneLocalVariable(localVariable, isReference);
      } else {
        Contract.Assume(false); // unexpected IVariable
        iv = null; // please compiler
      }

      return (VT)iv;
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
      return new FrameExpression(this, frame);
    }
    public Attributes CloneAttributes(Attributes attrs) {
      if (attrs == null) {
        return null;
      } else if (!CloneResolvedFields && attrs.Name.StartsWith("_")) {
        // skip this attribute, since it would have been produced during resolution
        return CloneAttributes(attrs.Prev);
      } else if (attrs is UserSuppliedAttributes) {
        var usa = (UserSuppliedAttributes)attrs;
        return new UserSuppliedAttributes(Tok(usa.tok), Tok(usa.OpenBrace), Tok(usa.CloseBrace), attrs.Args.ConvertAll(CloneExpr), CloneAttributes(attrs.Prev));
      } else {
        return new Attributes(attrs.Name, attrs.Args.ConvertAll(CloneExpr), CloneAttributes(attrs.Prev));
      }
    }

    public AttributedExpression CloneAttributedExpr(AttributedExpression expr) {
      var mfe = new AttributedExpression(CloneExpr(expr.E),
        expr.Label == null ? null : new AssertLabel(Tok(expr.Label.Tok), expr.Label.Name),
        CloneAttributes(expr.Attributes));
      mfe.Attributes = CloneAttributes(expr.Attributes);
      return mfe;
    }

    public virtual ActualBinding CloneActualBinding(ActualBinding binding) {
      return new ActualBinding(binding.FormalParameterName == null ? null : Tok(binding.FormalParameterName), CloneExpr(binding.Actual));
    }

    public virtual Expression CloneExpr(Expression expr) {
      if (expr == null) {
        return null;
      }

      if (expr is ICloneable<Expression> cloneableExpression) {
        return cloneableExpression.Clone(this);
      }

      var result = CloneExprInner(expr);
      if (CloneResolvedFields && expr.Type != null) {
        result.Type = expr.Type;
      }
      return result;
    }

    private Expression CloneExprInner(Expression expr) {
      if (expr is LiteralExpr) {
        var e = (LiteralExpr)expr;
        if (e is StaticReceiverExpr) {
          var ee = (StaticReceiverExpr)e;
          return new StaticReceiverExpr(Tok(e.tok), CloneType(ee.UnresolvedType), ee.IsImplicit);
        } else if (e.Value == null) {
          return new LiteralExpr(Tok(e.tok));
        } else if (e.Value is bool) {
          return new LiteralExpr(Tok(e.tok), (bool)e.Value);
        } else if (e is CharLiteralExpr) {
          return new CharLiteralExpr(Tok(e.tok), (string)e.Value);
        } else if (e is StringLiteralExpr) {
          var str = (StringLiteralExpr)e;
          return new StringLiteralExpr(Tok(e.tok), (string)e.Value, str.IsVerbatim);
        } else if (e.Value is BaseTypes.BigDec) {
          return new LiteralExpr(Tok(e.tok), (BaseTypes.BigDec)e.Value);
        } else {
          return new LiteralExpr(Tok(e.tok), (BigInteger)e.Value);
        }

      } else if (expr is ThisExpr) {
        if (expr is ImplicitThisExpr_ConstructorCall) {
          return new ImplicitThisExpr_ConstructorCall(Tok(expr.tok));
        } else if (expr is ImplicitThisExpr) {
          return new ImplicitThisExpr(Tok(expr.tok));
        } else {
          return new ThisExpr(Tok(expr.tok));
        }
      } else if (expr is AutoGhostIdentifierExpr) {
        var e = (AutoGhostIdentifierExpr)expr;
        return new AutoGhostIdentifierExpr(this, e);
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

      } else if (expr is SeqSelectExpr) {
        var e = (SeqSelectExpr)expr;
        return new SeqSelectExpr(Tok(e.tok), e.SelectOne, CloneExpr(e.Seq), CloneExpr(e.E0), CloneExpr(e.E1),
          Tok(e.CloseParen));
      } else if (expr is MultiSelectExpr) {
        var e = (MultiSelectExpr)expr;
        return new MultiSelectExpr(Tok(e.tok), CloneExpr(e.Array), e.Indices.ConvertAll(CloneExpr));

      } else if (expr is SeqUpdateExpr) {
        var e = (SeqUpdateExpr)expr;
        return new SeqUpdateExpr(Tok(e.tok), CloneExpr(e.Seq), CloneExpr(e.Index), CloneExpr(e.Value));

      } else if (expr is ApplyExpr) {
        var e = (ApplyExpr)expr;
        return new ApplyExpr(Tok(e.tok), CloneExpr(e.Function), e.Args.ConvertAll(CloneExpr), Tok(e.CloseParen));

      } else if (expr is SeqConstructionExpr) {
        var e = (SeqConstructionExpr)expr;
        var elemType = e.ExplicitElementType == null ? null : CloneType(e.ExplicitElementType);
        return new SeqConstructionExpr(Tok(e.tok), elemType, CloneExpr(e.N), CloneExpr(e.Initializer));

      } else if (expr is MultiSetFormingExpr) {
        var e = (MultiSetFormingExpr)expr;
        return new MultiSetFormingExpr(Tok(e.tok), CloneExpr(e.E));
      } else if (expr is UnaryOpExpr) {
        var e = (UnaryOpExpr)expr;
        return new UnaryOpExpr(Tok(e.tok), e.Op, CloneExpr(e.E));

      } else if (expr is ConversionExpr) {
        var e = (ConversionExpr)expr;
        return new ConversionExpr(Tok(e.tok), CloneExpr(e.E), CloneType(e.ToType));

      } else if (expr is TypeTestExpr) {
        var e = (TypeTestExpr)expr;
        return new TypeTestExpr(Tok(e.tok), CloneExpr(e.E), CloneType(e.ToType));
      } else if (expr is TernaryExpr) {
        var e = (TernaryExpr)expr;
        return new TernaryExpr(Tok(e.tok), e.Op, CloneExpr(e.E0), CloneExpr(e.E1), CloneExpr(e.E2));
      } else if (expr is WildcardExpr) {
        return new WildcardExpr(Tok(expr.tok));
      } else if (expr is StmtExpr) {
        var e = (StmtExpr)expr;
        return new StmtExpr(Tok(e.tok), CloneStmt(e.S), CloneExpr(e.E));
      } else if (expr is ITEExpr) {
        var e = (ITEExpr)expr;
        return new ITEExpr(Tok(e.tok), e.IsBindingGuard, CloneExpr(e.Test), CloneExpr(e.Thn), CloneExpr(e.Els));
      } else if (expr is ParensExpression) {
        var e = (ParensExpression)expr;
        return CloneExpr(e.E); // skip the parentheses in the clone
      }
      if (expr is Resolver_IdentifierExpr resolverIdentifierExpr) {
        return new Resolver_IdentifierExpr(Tok(resolverIdentifierExpr.tok), resolverIdentifierExpr.Decl, resolverIdentifierExpr.TypeArgs);
      } else {
        Contract.Assert(false);
        throw new cce.UnreachableException(); // unexpected expression
      }
    }

    public MatchCaseExpr CloneMatchCaseExpr(MatchCaseExpr c) {
      Contract.Requires(c != null);
      Contract.Requires(c.Arguments != null);
      return new MatchCaseExpr(Tok(c.tok), c.Ctor, c.FromBoundVar, c.Arguments.ConvertAll(bv => CloneBoundVar(bv, false)), CloneExpr(c.Body), CloneAttributes(c.Attributes));
    }

    public NestedMatchCaseExpr CloneNestedMatchCaseExpr(NestedMatchCaseExpr c) {
      Contract.Requires(c != null);
      return new NestedMatchCaseExpr(Tok(c.Tok), CloneExtendedPattern(c.Pat), CloneExpr(c.Body), CloneAttributes(c.Attributes));
    }

    public virtual CasePattern<VT> CloneCasePattern<VT>(CasePattern<VT> pat)
      where VT : class, IVariable {
      Contract.Requires(pat != null);
      return new CasePattern<VT>(this, pat);
    }

    public virtual NameSegment CloneNameSegment(Expression expr) {
      return new NameSegment(this, (NameSegment)expr);
    }

    public virtual AssignmentRhs CloneRHS(AssignmentRhs rhs) {
      AssignmentRhs c;
      if (rhs is ICloneable<AssignmentRhs> cloneable) {
        return cloneable.Clone(this);
      }

      if (rhs is ExprRhs) {
        var r = (ExprRhs)rhs;
        c = new ExprRhs(CloneExpr(r.Expr), CloneAttributes(rhs.Attributes));
      } else if (rhs is HavocRhs) {
        c = new HavocRhs(Tok(rhs.Tok));
      } else {
        throw new cce.UnreachableException();
      }
      return c;
    }

    public virtual BlockStmt CloneBlockStmt(BlockStmt stmt) {
      Contract.Requires(!(stmt is DividedBlockStmt));  // for blocks that may be DividedBlockStmt's, call CloneDividedBlockStmt instead
      if (stmt == null) {
        return null;
      } else {
        return new BlockStmt(Tok(stmt.Tok), Tok(stmt.EndTok), stmt.Body.ConvertAll(CloneStmt));
      }
    }

    public virtual DividedBlockStmt CloneDividedBlockStmt(DividedBlockStmt stmt) {
      if (stmt == null) {
        return null;
      } else {
        return new DividedBlockStmt(Tok(stmt.Tok), Tok(stmt.EndTok), stmt.BodyInit.ConvertAll(CloneStmt), stmt.SeparatorTok == null ? null : Tok(stmt.SeparatorTok), stmt.BodyProper.ConvertAll(CloneStmt));
      }
    }

    public virtual Statement CloneStmt(Statement stmt) {
      if (stmt == null) {
        return null;
      }

      if (statementClones.TryGetValue(stmt, out var cachedResult)) {
        return cachedResult;
      }

      if (stmt is ICloneable<Statement> cloneable) {
        var r = cloneable.Clone(this);
        // add labels to the cloned statement
        AddStmtLabels(r, stmt.Labels);
        r.Attributes = CloneAttributes(stmt.Attributes);

        return r;
      }

      Contract.Assert(false); throw new cce.UnreachableException();  // unexpected statement TODO, make all statements inherit from ICloneable.
    }

    public MatchCaseStmt CloneMatchCaseStmt(MatchCaseStmt c) {
      Contract.Requires(c != null);
      Contract.Assert(c.Arguments != null);
      return new MatchCaseStmt(Tok(c.tok), c.Ctor, c.FromBoundVar, c.Arguments.ConvertAll(v => CloneBoundVar(v, false)),
        c.Body.ConvertAll(CloneStmt), CloneAttributes(c.Attributes));
    }

    public ExtendedPattern CloneExtendedPattern(ExtendedPattern pat) {
      switch (pat) {
        case LitPattern p:
          return new LitPattern(p.Tok, CloneExpr(p.OrigLit));
        case IdPattern p:
          return new IdPattern(this, p);
        case DisjunctivePattern p:
          return new DisjunctivePattern(p.Tok, p.Alternatives.ConvertAll(CloneExtendedPattern), p.IsGhost);
        default:
          Contract.Assert(false);
          return null;
      }
    }
    public NestedMatchCaseStmt CloneNestedMatchCaseStmt(NestedMatchCaseStmt c) {
      Contract.Requires(c != null);
      return new NestedMatchCaseStmt(c.Tok, CloneExtendedPattern(c.Pat), c.Body.ConvertAll(CloneStmt), CloneAttributes(c.Attributes));
    }
    public CalcStmt.CalcOp CloneCalcOp(CalcStmt.CalcOp op) {
      if (op == null) {
        return null;
      } else if (op is CalcStmt.BinaryCalcOp) {
        return new CalcStmt.BinaryCalcOp(((CalcStmt.BinaryCalcOp)op).Op);
      } else if (op is CalcStmt.TernaryCalcOp) {
        return new CalcStmt.TernaryCalcOp(CloneExpr(((CalcStmt.TernaryCalcOp)op).Index));
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
      return new GuardedAlternative(Tok(alt.Tok), alt.IsBindingGuard, CloneExpr(alt.Guard), alt.Body.ConvertAll(CloneStmt), CloneAttributes(alt.Attributes));
    }

    public virtual Field CloneField(Field f) {
      Contract.Requires(f != null);
      return f switch {
        ConstantField c => new ConstantField(Tok(c.tok), c.Name, CloneExpr(c.Rhs), c.HasStaticKeyword, c.IsGhost, CloneType(c.Type), CloneAttributes(c.Attributes)),
        // We don't expect a SpecialField to ever be cloned. However, it can happen for malformed programs, for example if
        // an iterator in a refined module is replaced by a class in the refining module.
        SpecialField s => new SpecialField(Tok(s.tok), s.Name, s.SpecialId, s.IdParam, s.IsGhost, s.IsMutable, s.IsUserMutable, CloneType(s.Type), CloneAttributes(s.Attributes)),
        _ => new Field(Tok(f.tok), f.Name, f.HasStaticKeyword, f.IsGhost, f.IsMutable, f.IsUserMutable, CloneType(f.Type), CloneAttributes(f.Attributes))
      };
    }

    public virtual Function CloneFunction(Function f, string newName = null) {
      var tps = f.TypeArgs.ConvertAll(CloneTypeParam);
      var formals = f.Formals.ConvertAll(p => CloneFormal(p, false));
      var result = f.Result != null ? CloneFormal(f.Result, false) : null;
      var req = f.Req.ConvertAll(CloneAttributedExpr);
      var reads = f.Reads.ConvertAll(CloneFrameExpr);
      var decreases = CloneSpecExpr(f.Decreases);
      var ens = f.Ens.ConvertAll(CloneAttributedExpr);
      Expression body = CloneExpr(f.Body);
      BlockStmt byMethodBody = CloneBlockStmt(f.ByMethodBody);

      if (newName == null) {
        newName = f.Name;
      }

      if (f is Predicate) {
        return new Predicate(Tok(f.tok), newName, f.HasStaticKeyword, f.IsGhost, tps, formals, result,
          req, reads, ens, decreases, body, Predicate.BodyOriginKind.OriginalOrInherited,
          f.ByMethodTok == null ? null : Tok(f.ByMethodTok), byMethodBody,
          CloneAttributes(f.Attributes), null);
      } else if (f is LeastPredicate) {
        return new LeastPredicate(Tok(f.tok), newName, f.HasStaticKeyword, ((LeastPredicate)f).TypeOfK, tps, formals, result,
          req, reads, ens, body, CloneAttributes(f.Attributes), null);
      } else if (f is GreatestPredicate greatestPredicate) {
        return new GreatestPredicate(Tok(f.tok), newName, f.HasStaticKeyword, ((GreatestPredicate)f).TypeOfK, tps, formals, result,
          req, reads, ens, body, CloneAttributes(f.Attributes), null);
      } else if (f is TwoStatePredicate) {
        return new TwoStatePredicate(Tok(f.tok), newName, f.HasStaticKeyword, tps, formals, result,
          req, reads, ens, decreases, body, CloneAttributes(f.Attributes), null);
      } else if (f is TwoStateFunction) {
        return new TwoStateFunction(Tok(f.tok), newName, f.HasStaticKeyword, tps, formals, result, CloneType(f.ResultType),
          req, reads, ens, decreases, body, CloneAttributes(f.Attributes), null);
      } else {
        return new Function(Tok(f.tok), newName, f.HasStaticKeyword, f.IsGhost, tps, formals, result, CloneType(f.ResultType),
          req, reads, ens, decreases, body, f.ByMethodTok == null ? null : Tok(f.ByMethodTok), byMethodBody,
          CloneAttributes(f.Attributes), null);
      }
    }

    public virtual Method CloneMethod(Method m) {
      Contract.Requires(m != null);

      var tps = CloneResolvedFields ? m.TypeArgs : m.TypeArgs.ConvertAll(CloneTypeParam);
      var ins = m.Ins.ConvertAll(p => CloneFormal(p, false));
      var req = m.Req.ConvertAll(CloneAttributedExpr);
      var mod = CloneSpecFrameExpr(m.Mod);
      var decreases = CloneSpecExpr(m.Decreases);

      var ens = m.Ens.ConvertAll(CloneAttributedExpr);

      BlockStmt body = CloneMethodBody(m);

      if (m is Constructor) {
        return new Constructor(Tok(m.tok), m.Name, m.IsGhost, tps, ins,
          req, mod, ens, decreases, (DividedBlockStmt)body, CloneAttributes(m.Attributes), null);
      } else if (m is LeastLemma) {
        return new LeastLemma(Tok(m.tok), m.Name, m.HasStaticKeyword, ((LeastLemma)m).TypeOfK, tps, ins, m.Outs.ConvertAll(o => CloneFormal(o, false)),
          req, mod, ens, decreases, body, CloneAttributes(m.Attributes), null);
      } else if (m is GreatestLemma) {
        return new GreatestLemma(Tok(m.tok), m.Name, m.HasStaticKeyword, ((GreatestLemma)m).TypeOfK, tps, ins, m.Outs.ConvertAll(o => CloneFormal(o, false)),
          req, mod, ens, decreases, body, CloneAttributes(m.Attributes), null);
      } else if (m is Lemma) {
        return new Lemma(Tok(m.tok), m.Name, m.HasStaticKeyword, tps, ins, m.Outs.ConvertAll(o => CloneFormal(o, false)),
          req, mod, ens, decreases, body, CloneAttributes(m.Attributes), null);
      } else if (m is TwoStateLemma) {
        var two = (TwoStateLemma)m;
        return new TwoStateLemma(Tok(m.tok), m.Name, m.HasStaticKeyword, tps, ins, m.Outs.ConvertAll(o => CloneFormal(o, false)),
          req, mod, ens, decreases, body, CloneAttributes(m.Attributes), null);
      } else {
        return new Method(Tok(m.tok), m.Name, m.HasStaticKeyword, m.IsGhost, tps, ins, m.Outs.ConvertAll(o => CloneFormal(o, false)),
          req, mod, ens, decreases, body, CloneAttributes(m.Attributes), null, m.IsByMethod);
      }
    }

    public virtual BlockStmt CloneMethodBody(Method m) {
      if (m.Body is DividedBlockStmt) {
        return CloneDividedBlockStmt((DividedBlockStmt)m.Body);
      } else {
        return CloneBlockStmt(m.Body);
      }
    }

    public virtual IToken Tok(IToken tok) {
      Contract.Requires(tok != null);
      return tok;
    }

    public virtual AttributedToken AttributedTok(AttributedToken tok) {
      if (tok == null) {
        return null;
      }
      return new AttributedToken(Tok(tok.Token), CloneAttributes(tok.Attrs));
    }
  }

  public class ClonerKeepParensExpressions : Cloner {
    public override Expression CloneExpr(Expression expr) {
      if (expr is ParensExpression parensExpression) {
        return new ParensExpression(Tok(parensExpression.tok), CloneExpr(parensExpression.E));
      }
      return base.CloneExpr(expr);
    }
  }

  /// <summary>
  /// This cloner copies the origin module signatures to their cloned declarations
  /// </summary>
  class DeepModuleSignatureCloner : Cloner {
    public override TopLevelDecl CloneDeclaration(TopLevelDecl d, ModuleDefinition m) {
      var dd = base.CloneDeclaration(d, m);
      if (d is ModuleDecl) {
        ((ModuleDecl)dd).Signature = ((ModuleDecl)d).Signature;
        if (d is AbstractModuleDecl) {
          var sourcefacade = (AbstractModuleDecl)d;

          ((AbstractModuleDecl)dd).OriginalSignature = sourcefacade.OriginalSignature;
          if (sourcefacade.QId.Root != null) {
            ((AbstractModuleDecl)dd).QId.SetRoot((ModuleDecl)CloneDeclaration(sourcefacade.QId.Root, m));
          }
        } else if (d is AliasModuleDecl) {
          var sourcealias = (AliasModuleDecl)d;

          if (sourcealias.TargetQId.Root != null) {
            ((AliasModuleDecl)dd).TargetQId.SetRoot((ModuleDecl)CloneDeclaration(sourcealias.TargetQId.Root, m));
          }
        }
      }
      return dd;
    }
  }


  class ScopeCloner : DeepModuleSignatureCloner {
    private VisibilityScope scope = null;

    private Dictionary<Declaration, Declaration> reverseMap = new Dictionary<Declaration, Declaration>();

    private bool isInvisibleClone(Declaration d) {
      Contract.Assert(reverseMap.ContainsKey(d));
      return !reverseMap[d].IsVisibleInScope(scope);
    }

    public ScopeCloner(VisibilityScope scope) {
      this.scope = scope;
    }

    private bool RevealedInScope(Declaration d) {
      return d.IsRevealedInScope(scope);
    }

    private bool VisibleInScope(Declaration d) {
      return d.IsVisibleInScope(scope);
    }

    public override ModuleDefinition CloneModuleDefinition(ModuleDefinition m, string name) {
      var basem = base.CloneModuleDefinition(m, name);


      //Merge signatures for imports which point to the same module
      //This makes the consistency check understand that the same element
      //may be referred to via different qualifications.
      var sigmap = new Dictionary<ModuleDefinition, ModuleSignature>();
      var declmap = new Dictionary<ModuleDefinition, List<AliasModuleDecl>>();
      var vismap = new Dictionary<ModuleDefinition, VisibilityScope>();

      foreach (var top in basem.TopLevelDecls) {
        var import = reverseMap[top] as AliasModuleDecl;
        if (import == null) {
          continue;
        }

        var def = import.Signature.ModuleDef;
        if (def == null) {
          continue;
        }

        if (!declmap.ContainsKey(def)) {
          declmap.Add(def, new List<AliasModuleDecl>());
          sigmap.Add(def, new ModuleSignature());
          vismap.Add(def, new VisibilityScope());
        }

        sigmap[def] = Resolver.MergeSignature(sigmap[def], import.Signature);
        sigmap[def].ModuleDef = def;
        declmap[def].Add((AliasModuleDecl)top);
        if (VisibleInScope(import)) {
          vismap[def].Augment(import.Signature.VisibilityScope);
        }

      }

      foreach (var decls in declmap) {
        sigmap[decls.Key].VisibilityScope = vismap[decls.Key];
        foreach (var decl in decls.Value) {
          decl.Signature = sigmap[decls.Key];
        }
      }

      basem.TopLevelDecls.RemoveAll(t => {
        if (t is AliasModuleDecl aliasModuleDecl) {
          var def = aliasModuleDecl.Signature.ModuleDef;
          return def != null && vismap[def].IsEmpty();
        }

        return isInvisibleClone(t);
      });

      basem.TopLevelDecls.OfType<TopLevelDeclWithMembers>().
        Iter(t => t.Members.RemoveAll(isInvisibleClone));

      return basem;
    }

    public override TopLevelDecl CloneDeclaration(TopLevelDecl d, ModuleDefinition m) {
      var based = base.CloneDeclaration(d, m);
      if ((d is RevealableTypeDecl || d is TopLevelDeclWithMembers) && !(d is ClassDecl cd && cd.NonNullTypeDecl == null) && !RevealedInScope(d)) {
        var tps = d.TypeArgs.ConvertAll(CloneTypeParam);
        var characteristics = TypeParameter.GetExplicitCharacteristics(d);
        var members = based is TopLevelDeclWithMembers tm ? tm.Members : new List<MemberDecl>();
        var otd = new OpaqueTypeDecl(Tok(d.tok), d.Name, m, characteristics, tps, members, CloneAttributes(d.Attributes), d.IsRefining);
        based = otd;
        if (d is ClassDecl) {
          reverseMap.Add(based, ((ClassDecl)d).NonNullTypeDecl);
          return based;
        }
      }

      reverseMap.Add(based, d);
      return based;

    }

    public override Field CloneField(Field f) {
      var cf = f as ConstantField;
      if (cf != null && cf.Rhs != null && !RevealedInScope(f)) {
        // We erase the RHS value. While we do that, we must also make sure the declaration does have a type, so instead of
        // cloning cf.Type, we assume "f" has been resolved and clone cf.Type.NormalizeExpandKeepConstraints().
        return new ConstantField(Tok(cf.tok), cf.Name, null, cf.IsStatic, cf.IsGhost, CloneType(cf.Type.NormalizeExpandKeepConstraints()), CloneAttributes(cf.Attributes));
      }
      return base.CloneField(f);
    }

    public override Function CloneFunction(Function f, string newName = null) {
      var basef = base.CloneFunction(f, newName);
      if (basef.ByMethodBody != null) {
        Contract.Assert(!basef.IsGhost); // a function-by-method has .IsGhost == false
        Contract.Assert(basef.Body != null); // a function-by-method has a nonempty .Body
        if (RevealedInScope(f)) {
          // For an "export reveals", use an empty (but not absent) by-method part.
          basef.ByMethodBody = new BlockStmt(basef.ByMethodBody.Tok, basef.ByMethodBody.EndTok, new List<Statement>());
        } else {
          // For an "export provides", remove the by-method part altogether.
          basef.ByMethodTok = null;
          basef.ByMethodBody = null;
        }
      }
      if (!RevealedInScope(f)) {
        basef.Body = null;
      }
      return basef;
    }

    public override Method CloneMethod(Method m) {
      var basem = base.CloneMethod(m);
      basem.Body = null; //exports never reveal method bodies
      return basem;
    }

    public override MemberDecl CloneMember(MemberDecl member, bool isReference) {
      var basem = base.CloneMember(member, isReference);
      reverseMap.Add(basem, member);
      return basem;
    }

  }

  /// <summary>
  /// This cloner is used during the creation of a module signature for a method facade.
  /// It does not clone method bodies, and it copies module signatures.
  /// </summary>
  class ClonerButDropMethodBodies : DeepModuleSignatureCloner {
    public ClonerButDropMethodBodies()
      : base() {
    }

    public override BlockStmt CloneBlockStmt(BlockStmt stmt) {
      return null;
    }
  }

  class AbstractSignatureCloner : ScopeCloner {

    public AbstractSignatureCloner(VisibilityScope scope)
      : base(scope) {
    }

    public override ModuleDefinition CloneModuleDefinition(ModuleDefinition m, string name) {
      var basem = base.CloneModuleDefinition(m, name);
      basem.TopLevelDecls.RemoveAll(t => t is ModuleExportDecl);
      return basem;
    }

    public override BlockStmt CloneMethodBody(Method m) {
      return null;
    }
  }



  /// <summary>
  /// This cloner is used to clone a module into a _Compile module.  This is different from
  /// the standard cloner in the following ways:
  ///  TODO remove this behavior since it's no longer needed.
  /// * "match" statements and "match" expressions obtain their original form, which may include
  ///   nested patterns.  The resolver will turn these into nested "match" constructs with simple
  ///   patterns.
  /// * The various module-signature fields of modules are set to whatever they were in the original.
  /// * To get the .RefinementBase, it redirects using the given mapping
  /// </summary>
  class CompilationCloner : DeepModuleSignatureCloner {
    Dictionary<ModuleDefinition, ModuleDefinition> compilationModuleClones;
    public CompilationCloner(Dictionary<ModuleDefinition, ModuleDefinition> compilationModuleClones)
      : base() {
      this.compilationModuleClones = compilationModuleClones;
    }

    public override TopLevelDecl CloneDeclaration(TopLevelDecl d, ModuleDefinition m) {
      var r = base.CloneDeclaration(d, m);
      if (d is AliasModuleDecl importDeclSource) {
        var importDeclClone = (AliasModuleDecl)r;  // if d is AliasModuleDecl, then we expect base to return an AliasModuleDecl
        importDeclClone.ShadowsLiteralModule = importDeclSource.ShadowsLiteralModule;
      }
      return r;
    }

    public override Expression CloneExpr(Expression expr) {
      var me = expr as MatchExpr;
      if (me != null && me.OrigUnresolved != null) {
        return CloneExpr(me.OrigUnresolved);
      }
      return base.CloneExpr(expr);
    }

    public ModuleSignature CloneModuleSignature(ModuleSignature org, ModuleSignature newSig) {
      var sig = new ModuleSignature();
      sig.ModuleDef = newSig.ModuleDef;
      sig.IsAbstract = newSig.IsAbstract;
      sig.VisibilityScope = new VisibilityScope();
      sig.VisibilityScope.Augment(newSig.VisibilityScope);

      foreach (var kv in org.TopLevels) {
        TopLevelDecl d;
        if (newSig.TopLevels.TryGetValue(kv.Key, out d)) {
          sig.TopLevels.Add(kv.Key, d);
        }
      }

      foreach (var kv in org.ExportSets) {
        ModuleExportDecl d;
        if (newSig.ExportSets.TryGetValue(kv.Key, out d)) {
          sig.ExportSets.Add(kv.Key, d);
        }
      }

      foreach (var kv in org.Ctors) {
        Tuple<DatatypeCtor, bool> pair;
        if (newSig.Ctors.TryGetValue(kv.Key, out pair)) {
          sig.Ctors.Add(kv.Key, pair);
        }
      }

      foreach (var kv in org.StaticMembers) {
        MemberDecl md;
        if (newSig.StaticMembers.TryGetValue(kv.Key, out md)) {
          sig.StaticMembers.Add(kv.Key, md);
        }
      }
      return sig;
    }
  }

}
