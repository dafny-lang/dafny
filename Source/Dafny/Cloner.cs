// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

using System;
using System.Collections.Generic;
using System.Numerics;
using System.Diagnostics.Contracts;
using System.Linq;
using Microsoft.Boogie;
using IToken = Microsoft.Boogie.IToken;

namespace Microsoft.Dafny
{
  class Cloner
  {


    public virtual ModuleDefinition CloneModuleDefinition(ModuleDefinition m, string name) {
      ModuleDefinition nw;
      if (m is DefaultModuleDecl) {
        nw = new DefaultModuleDecl();
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
        return new OpaqueTypeDecl(Tok(dd.tok), dd.Name, m, CloneTPChar(dd.Characteristics), dd.TypeArgs.ConvertAll(CloneTypeParam), dd.Members.ConvertAll(CloneMember), CloneAttributes(dd.Attributes), dd.IsRefining);
      } else if (d is SubsetTypeDecl) {
        Contract.Assume(!(d is NonNullTypeDecl));  // don't clone the non-null type declaration; close the class, which will create a new non-null type declaration
        var dd = (SubsetTypeDecl)d;
        var tps = dd.TypeArgs.ConvertAll(CloneTypeParam);
        return new SubsetTypeDecl(Tok(dd.tok), dd.Name, CloneTPChar(dd.Characteristics), tps, m, CloneBoundVar(dd.Var), CloneExpr(dd.Constraint), dd.WitnessKind, CloneExpr(dd.Witness), CloneAttributes(dd.Attributes));
      } else if (d is TypeSynonymDecl) {
        var dd = (TypeSynonymDecl)d;
        var tps = dd.TypeArgs.ConvertAll(CloneTypeParam);
        return new TypeSynonymDecl(Tok(dd.tok), dd.Name, CloneTPChar(dd.Characteristics), tps, m, CloneType(dd.Rhs), CloneAttributes(dd.Attributes));
      } else if (d is NewtypeDecl) {
        var dd = (NewtypeDecl)d;
          if (dd.Var == null) {
            return new NewtypeDecl(Tok(dd.tok), dd.Name, m, CloneType(dd.BaseType), dd.Members.ConvertAll(CloneMember), CloneAttributes(dd.Attributes), dd.IsRefining);
          } else {
            return new NewtypeDecl(Tok(dd.tok), dd.Name, m, CloneBoundVar(dd.Var), CloneExpr(dd.Constraint), dd.WitnessKind, CloneExpr(dd.Witness), dd.Members.ConvertAll(CloneMember), CloneAttributes(dd.Attributes), dd.IsRefining);
          }
      } else if (d is TupleTypeDecl) {
        var dd = (TupleTypeDecl)d;
        return new TupleTypeDecl(dd.ArgumentGhostness, dd.EnclosingModuleDefinition, dd.Attributes);
      } else if (d is IndDatatypeDecl) {
        var dd = (IndDatatypeDecl)d;
        var tps = dd.TypeArgs.ConvertAll(CloneTypeParam);
        var ctors = dd.Ctors.ConvertAll(CloneCtor);
        var dt = new IndDatatypeDecl(Tok(dd.tok), dd.Name, m, tps, ctors, dd.Members.ConvertAll(CloneMember), CloneAttributes(dd.Attributes), dd.IsRefining);
        return dt;
      } else if (d is CoDatatypeDecl) {
        var dd = (CoDatatypeDecl)d;
        var tps = dd.TypeArgs.ConvertAll(CloneTypeParam);
        var ctors = dd.Ctors.ConvertAll(CloneCtor);
        var dt = new CoDatatypeDecl(Tok(dd.tok), dd.Name, m, tps, ctors, dd.Members.ConvertAll(CloneMember), CloneAttributes(dd.Attributes), dd.IsRefining);
        return dt;
      } else if (d is IteratorDecl) {
        var dd = (IteratorDecl)d;
        var tps = dd.TypeArgs.ConvertAll(CloneTypeParam);
        var ins = dd.Ins.ConvertAll(CloneFormal);
        var outs = dd.Outs.ConvertAll(CloneFormal);
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
        var mm = dd.Members.ConvertAll(CloneMember);
        var cl = new TraitDecl(Tok(dd.tok), dd.Name, m, tps, mm, CloneAttributes(dd.Attributes), dd.IsRefining, dd.ParentTraits.ConvertAll(CloneType));
        return cl;
      } else if (d is ClassDecl) {
        var dd = (ClassDecl)d;
        var tps = dd.TypeArgs.ConvertAll(CloneTypeParam);
        var mm = dd.Members.ConvertAll(CloneMember);
        if (d is DefaultClassDecl) {
          return new DefaultClassDecl(m, mm);
        } else {
          return new ClassDecl(Tok(dd.tok), dd.Name, m, tps, mm, CloneAttributes(dd.Attributes), dd.IsRefining, dd.ParentTraits.ConvertAll(CloneType));
        }
      } else if (d is ModuleDecl) {
        if (d is LiteralModuleDecl) {
          // TODO: Does not clone any details; is still resolved
          return new LiteralModuleDecl(((LiteralModuleDecl)d).ModuleDef, m);
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
      return new DatatypeCtor(Tok(ct.tok), ct.Name, ct.Formals.ConvertAll(CloneFormal), CloneAttributes(ct.Attributes));
    }

    public TypeParameter CloneTypeParam(TypeParameter tp) {
      return new TypeParameter(Tok(tp.tok), tp.Name, tp.VarianceSyntax, CloneTPChar(tp.Characteristics));
    }

    public virtual MemberDecl CloneMember(MemberDecl member) {
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
      } else if (t is ParamTypeProxy) {
        return new ParamTypeProxy(CloneTypeParam(((ParamTypeProxy)t).orig));
      } else {
        Contract.Assert(false);  // unexpected type (e.g., no other type proxies are expected at this time)
        return null;  // to please compiler
      }
    }

    public Formal CloneFormal(Formal formal) {
      Formal f = new Formal(Tok(formal.tok), formal.Name, CloneType(formal.Type), formal.InParam, formal.IsGhost,
        CloneExpr(formal.DefaultValue), formal.IsOld);
      return f;
    }

    public virtual BoundVar CloneBoundVar(BoundVar bv) {
      var bvNew = new BoundVar(Tok(bv.tok), bv.Name, CloneType(bv.SyntacticType));
      bvNew.IsGhost = bv.IsGhost;
      return bvNew;
    }

    public VT CloneIVariable<VT>(VT v) where VT: IVariable {
      var iv = (IVariable)v;
      if (iv is Formal) {
        iv = CloneFormal((Formal)iv);
      } else if (iv is BoundVar) {
        iv = CloneBoundVar((BoundVar)iv);
      } else if (iv is LocalVariable) {
        var local = (LocalVariable)iv;
        iv = new LocalVariable(Tok(local.Tok), Tok(local.EndTok), local.Name, CloneType(local.OptionalType), local.IsGhost);
      } else {
        Contract.Assume(false);  // unexpected IVariable
        iv = null;  // please compiler
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
        return new UserSuppliedAttributes(Tok(usa.tok), Tok(usa.OpenBrace), Tok(usa.CloseBrace), attrs.Args.ConvertAll(CloneExpr), CloneAttributes(attrs.Prev));
      } else {
        return new Attributes(attrs.Name, attrs.Args.ConvertAll(CloneExpr), CloneAttributes(attrs.Prev));
      }
    }

    public AttributedExpression CloneAttributedExpr(AttributedExpression expr) {
      var mfe = new AttributedExpression(CloneExpr(expr.E), expr.Label == null ? null : new AssertLabel(Tok(expr.Label.Tok), expr.Label.Name), CloneAttributes(expr.Attributes));
      mfe.Attributes = CloneAttributes(expr.Attributes);
      return mfe;
    }

    public virtual ActualBinding CloneActualBinding(ActualBinding binding) {
      return new ActualBinding(binding.FormalParameterName == null ? null : Tok(binding.FormalParameterName), CloneExpr(binding.Actual));
    }

    public virtual Expression CloneExpr(Expression expr) {
      if (expr == null) {
        return null;
      } else if (expr is LiteralExpr) {
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
        return new AutoGhostIdentifierExpr(Tok(e.tok), e.Name);

      } else if (expr is IdentifierExpr) {
        var e = (IdentifierExpr)expr;
        return new IdentifierExpr(Tok(e.tok), e.Name);

      } else if (expr is DatatypeValue) {
        var e = (DatatypeValue)expr;
        return new DatatypeValue(Tok(e.tok), e.DatatypeName, e.MemberName, e.Bindings.ArgumentBindings.ConvertAll(CloneActualBinding));

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
        return new FunctionCallExpr(Tok(e.tok), e.Name, CloneExpr(e.Receiver), e.OpenParen == null ? null : Tok(e.OpenParen), e.Bindings.ArgumentBindings.ConvertAll(CloneActualBinding), e.AtLabel);

      } else if (expr is ApplyExpr) {
        var e = (ApplyExpr)expr;
        return new ApplyExpr(Tok(e.tok), CloneExpr(e.Function), e.Args.ConvertAll(CloneExpr));

      } else if (expr is SeqConstructionExpr) {
        var e = (SeqConstructionExpr)expr;
        var elemType = e.ExplicitElementType == null ? null : CloneType(e.ExplicitElementType);
        return new SeqConstructionExpr(Tok(e.tok), elemType, CloneExpr(e.N), CloneExpr(e.Initializer));

      } else if (expr is MultiSetFormingExpr) {
        var e = (MultiSetFormingExpr)expr;
        return new MultiSetFormingExpr(Tok(e.tok), CloneExpr(e.E));

      } else if (expr is OldExpr) {
        var e = (OldExpr)expr;
        return new OldExpr(Tok(e.tok), CloneExpr(e.E), e.At);

      } else if (expr is UnchangedExpr) {
        var e = (UnchangedExpr)expr;
        return new UnchangedExpr(Tok(e.tok), e.Frame.ConvertAll(CloneFrameExpr), e.At);

      } else if (expr is UnaryOpExpr) {
        var e = (UnaryOpExpr)expr;
        return new UnaryOpExpr(Tok(e.tok), e.Op, CloneExpr(e.E));

      } else if (expr is ConversionExpr) {
        var e = (ConversionExpr)expr;
        return new ConversionExpr(Tok(e.tok), CloneExpr(e.E), CloneType(e.ToType));

      } else if (expr is TypeTestExpr) {
        var e = (TypeTestExpr)expr;
        return new TypeTestExpr(Tok(e.tok), CloneExpr(e.E), CloneType(e.ToType));

      } else if (expr is BinaryExpr) {
        var e = (BinaryExpr)expr;
        return new BinaryExpr(Tok(e.tok), e.Op, CloneExpr(e.E0), CloneExpr(e.E1));

      } else if (expr is TernaryExpr) {
        var e = (TernaryExpr)expr;
        return new TernaryExpr(Tok(e.tok), e.Op, CloneExpr(e.E0), CloneExpr(e.E1), CloneExpr(e.E2));

      } else if (expr is ChainingExpression) {
        var e = (ChainingExpression)expr;
        return new ChainingExpression(Tok(e.tok), e.Operands.ConvertAll(CloneExpr), e.Operators, e.OperatorLocs.ConvertAll(Tok), e.PrefixLimits.ConvertAll(CloneExpr));

      } else if (expr is LetExpr) {
        var e = (LetExpr)expr;
        return new LetExpr(Tok(e.tok), e.LHSs.ConvertAll(CloneCasePattern), e.RHSs.ConvertAll(CloneExpr), CloneExpr(e.Body), e.Exact, e.Attributes);

      } else if (expr is LetOrFailExpr) {
        var e = (LetOrFailExpr)expr;
        return new LetOrFailExpr(Tok(e.tok), e.Lhs == null ? null : CloneCasePattern(e.Lhs), CloneExpr(e.Rhs), CloneExpr(e.Body));

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
          var mc = (MapComprehension)e;
          return new MapComprehension(tk, mc.Finite, bvs, range, mc.TermLeft == null ? null : CloneExpr(mc.TermLeft), term, CloneAttributes(e.Attributes));
        } else if (e is LambdaExpr) {
          var l = (LambdaExpr)e;
          return new LambdaExpr(tk, bvs, range, l.Reads.ConvertAll(CloneFrameExpr), term);
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
        return new ITEExpr(Tok(e.tok), e.IsBindingGuard, CloneExpr(e.Test), CloneExpr(e.Thn), CloneExpr(e.Els));

      } else if (expr is AutoGeneratedExpression) {
        var e = (AutoGeneratedExpression)expr;
        var a = CloneExpr(e.E);
        return new AutoGeneratedExpression(Tok(e.tok), a);

      } else if (expr is ParensExpression) {
        var e = (ParensExpression)expr;
        return CloneExpr(e.E);  // skip the parentheses in the clone
      } else if (expr is NestedMatchExpr) {
        var e = (NestedMatchExpr) expr;
        return new NestedMatchExpr(Tok(e.tok), CloneExpr(e.Source), e.Cases.ConvertAll(CloneNestedMatchCaseExpr), e.UsesOptionalBraces);

      } else if (expr is MatchExpr) {
        var e = (MatchExpr)expr;
        return new MatchExpr(Tok(e.tok), CloneExpr(e.Source), e.Cases.ConvertAll(CloneMatchCaseExpr), e.UsesOptionalBraces);

      } else if (expr is NegationExpression) {
        var e = (NegationExpression)expr;
        return new NegationExpression(Tok(e.tok), CloneExpr(e.E));

      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected expression
      }
    }

    public MatchCaseExpr CloneMatchCaseExpr(MatchCaseExpr c) {
      Contract.Requires(c != null);
      Contract.Requires(c.Arguments != null);
      return new MatchCaseExpr(Tok(c.tok), c.Ctor, c.Arguments.ConvertAll(CloneBoundVar), CloneExpr(c.Body), CloneAttributes(c.Attributes));
    }

    public NestedMatchCaseExpr CloneNestedMatchCaseExpr(NestedMatchCaseExpr c) {
      Contract.Requires(c != null);
      return new NestedMatchCaseExpr(Tok(c.Tok), CloneExtendedPattern(c.Pat), CloneExpr(c.Body), CloneAttributes(c.Attributes));
    }

    public virtual Expression CloneApplySuffix(ApplySuffix e) {
        return new ApplySuffix(Tok(e.tok), e.AtTok == null ? null : Tok(e.AtTok), CloneExpr(e.Lhs), e.Bindings.ArgumentBindings.ConvertAll(CloneActualBinding));
    }

    public virtual CasePattern<VT> CloneCasePattern<VT>(CasePattern<VT> pat) where VT: IVariable {
      Contract.Requires(pat != null);
      if (pat.Var != null) {
        return new CasePattern<VT>(pat.tok, CloneIVariable(pat.Var));
      } else if (pat.Arguments == null) {
        return new CasePattern<VT>(pat.tok, pat.Id, null);
      } else {
        return new CasePattern<VT>(pat.tok, pat.Id, pat.Arguments.ConvertAll(CloneCasePattern));
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
          if (r.InitDisplay != null) {
            Contract.Assert(r.ArrayDimensions.Count == 1);
            c = new TypeRhs(Tok(r.Tok), CloneType(r.EType), CloneExpr(r.ArrayDimensions[0]), r.InitDisplay.ConvertAll(CloneExpr));
          } else {
            c = new TypeRhs(Tok(r.Tok), CloneType(r.EType), r.ArrayDimensions.ConvertAll(CloneExpr), CloneExpr(r.ElementInit));
          }
        } else if (r.Bindings == null) {
          c = new TypeRhs(Tok(r.Tok), CloneType(r.EType));
        } else {
          c = new TypeRhs(Tok(r.Tok), CloneType(r.Path), r.Bindings.ArgumentBindings.ConvertAll(CloneActualBinding));
        }
      }
      c.Attributes = CloneAttributes(rhs.Attributes);
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

      Statement r;
      if (stmt is AssertStmt) {
        var s = (AssertStmt)stmt;
        r = new AssertStmt(Tok(s.Tok), Tok(s.EndTok), CloneExpr(s.Expr), CloneBlockStmt(s.Proof), s.Label == null ? null : new AssertLabel(Tok(s.Label.Tok), s.Label.Name), null);

      } else if (stmt is ExpectStmt) {
        var s = (ExpectStmt)stmt;
        r = new ExpectStmt(Tok(s.Tok), Tok(s.EndTok), CloneExpr(s.Expr), CloneExpr(s.Message), CloneAttributes(s.Attributes));

      } else if (stmt is AssumeStmt) {
        var s = (AssumeStmt)stmt;
        r = new AssumeStmt(Tok(s.Tok), Tok(s.EndTok), CloneExpr(s.Expr), null);

      } else if (stmt is PrintStmt) {
        var s = (PrintStmt)stmt;
        r = new PrintStmt(Tok(s.Tok), Tok(s.EndTok), s.Args.ConvertAll(CloneExpr));

      } else if (stmt is RevealStmt) {
        var s = (RevealStmt)stmt;
        r = new RevealStmt(Tok(s.Tok), Tok(s.EndTok), s.Exprs.ConvertAll(CloneExpr));

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

      } else if (stmt is DividedBlockStmt) {
        r = CloneDividedBlockStmt((DividedBlockStmt)stmt);

      } else if (stmt is BlockStmt) {
        r = CloneBlockStmt((BlockStmt)stmt);

      } else if (stmt is IfStmt) {
        var s = (IfStmt)stmt;
        r = new IfStmt(Tok(s.Tok), Tok(s.EndTok), s.IsBindingGuard, CloneExpr(s.Guard), CloneBlockStmt(s.Thn), CloneStmt(s.Els));

      } else if (stmt is AlternativeStmt) {
        var s = (AlternativeStmt)stmt;
        r = new AlternativeStmt(Tok(s.Tok), Tok(s.EndTok), s.Alternatives.ConvertAll(CloneGuardedAlternative), s.UsesOptionalBraces, CloneAttributes(s.Attributes));

      } else if (stmt is WhileStmt) {
        var s = (WhileStmt)stmt;
        r = new WhileStmt(Tok(s.Tok), Tok(s.EndTok), CloneExpr(s.Guard),
          s.Invariants.ConvertAll(CloneAttributedExpr), CloneSpecExpr(s.Decreases), CloneSpecFrameExpr(s.Mod), CloneBlockStmt(s.Body), CloneAttributes(s.Attributes));

      } else if (stmt is ForLoopStmt) {
        var s = (ForLoopStmt)stmt;
        r = new ForLoopStmt(Tok(s.Tok), Tok(s.EndTok), CloneBoundVar(s.LoopIndex), CloneExpr(s.Start), CloneExpr(s.End), s.GoingUp,
          s.Invariants.ConvertAll(CloneAttributedExpr), CloneSpecExpr(s.Decreases), CloneSpecFrameExpr(s.Mod), CloneBlockStmt(s.Body), CloneAttributes(s.Attributes));

      } else if (stmt is AlternativeLoopStmt) {
        var s = (AlternativeLoopStmt)stmt;
        r = new AlternativeLoopStmt(Tok(s.Tok), Tok(s.EndTok), s.Invariants.ConvertAll(CloneAttributedExpr), CloneSpecExpr(s.Decreases), CloneSpecFrameExpr(s.Mod), s.Alternatives.ConvertAll(CloneGuardedAlternative), s.UsesOptionalBraces, CloneAttributes(s.Attributes));

      } else if (stmt is ForallStmt) {
        var s = (ForallStmt)stmt;
        r = new ForallStmt(Tok(s.Tok), Tok(s.EndTok), s.BoundVars.ConvertAll(CloneBoundVar), null, CloneExpr(s.Range), s.Ens.ConvertAll(CloneAttributedExpr), CloneStmt(s.Body));
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
        r = new CalcStmt(Tok(s.Tok), Tok(s.EndTok), CloneCalcOp(s.UserSuppliedOp), lines, s.Hints.ConvertAll(CloneBlockStmt), s.StepOps.ConvertAll(CloneCalcOp), CloneAttributes(s.Attributes));
      } else if (stmt is NestedMatchStmt) {
        var s = (NestedMatchStmt)stmt;
        r = new NestedMatchStmt(Tok(s.Tok), Tok(s.EndTok), CloneExpr(s.Source), s.Cases.ConvertAll(CloneNestedMatchCaseStmt), s.UsesOptionalBraces);

      } else if (stmt is MatchStmt) {
        var s = (MatchStmt)stmt;
        r = new MatchStmt(Tok(s.Tok), Tok(s.EndTok), CloneExpr(s.Source), s.Cases.ConvertAll(CloneMatchCaseStmt), s.UsesOptionalBraces);

      } else if (stmt is AssignSuchThatStmt) {
        var s = (AssignSuchThatStmt)stmt;
        r = new AssignSuchThatStmt(Tok(s.Tok), Tok(s.EndTok), s.Lhss.ConvertAll(CloneExpr), CloneExpr(s.Expr), s.AssumeToken == null ? null : Tok(s.AssumeToken), null);

      } else if (stmt is UpdateStmt) {
        var s = (UpdateStmt)stmt;
        r = new UpdateStmt(Tok(s.Tok), Tok(s.EndTok), s.Lhss.ConvertAll(CloneExpr), s.Rhss.ConvertAll(CloneRHS), s.CanMutateKnownState);

      } else if (stmt is AssignOrReturnStmt) {
        var s = (AssignOrReturnStmt)stmt;
        r = new AssignOrReturnStmt(Tok(s.Tok), Tok(s.EndTok), s.Lhss.ConvertAll(CloneExpr), CloneExpr(s.Rhs), s.KeywordToken == null ? null : Tok(s.KeywordToken), s.Rhss == null ? null : s.Rhss.ConvertAll(e => CloneRHS(e)));

      } else if (stmt is VarDeclStmt) {
        var s = (VarDeclStmt)stmt;
        var lhss = s.Locals.ConvertAll(c => new LocalVariable(Tok(c.Tok), Tok(c.EndTok), c.Name, CloneType(c.OptionalType), c.IsGhost));
        r = new VarDeclStmt(Tok(s.Tok), Tok(s.EndTok), lhss, (ConcreteUpdateStatement)CloneStmt(s.Update));

      } else if (stmt is VarDeclPattern) {
        var s = (VarDeclPattern) stmt;
        r = new VarDeclPattern(Tok(s.Tok), Tok(s.EndTok), CloneCasePattern(s.LHS), CloneExpr(s.RHS), s.HasGhostModifier);

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
      Contract.Assert(c.Arguments != null);
      return new MatchCaseStmt(Tok(c.tok), c.Ctor, c.Arguments.ConvertAll(CloneBoundVar), c.Body.ConvertAll(CloneStmt), CloneAttributes(c.Attributes));
    }

    public ExtendedPattern CloneExtendedPattern(ExtendedPattern pat) {
      if(pat is LitPattern) {
        var p = (LitPattern)pat;
        return new LitPattern(p.Tok, CloneExpr(p.OrigLit));
      } else if (pat is IdPattern) {
        var p = (IdPattern)pat;
        return new IdPattern(p.Tok, p.Id, p.Arguments == null ? null : p.Arguments.ConvertAll(CloneExtendedPattern));
      } else {
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
      return new GuardedAlternative(Tok(alt.Tok), alt.IsBindingGuard, CloneExpr(alt.Guard), alt.Body.ConvertAll(CloneStmt), CloneAttributes(alt.Attributes));
    }

    public virtual Field CloneField(Field f) {
      Contract.Requires(f != null);
      return f switch
      {
        ConstantField c => new ConstantField(Tok(c.tok), c.Name, CloneExpr(c.Rhs), c.HasStaticKeyword, c.IsGhost, CloneType(c.Type), CloneAttributes(c.Attributes)),
        // We don't expect a SpecialField to ever be cloned. However, it can happen for malformed programs, for example if
        // an iterator in a refined module is replaced by a class in the refining module.
        SpecialField s => new SpecialField(Tok(s.tok), s.Name, s.SpecialId, s.IdParam, s.IsGhost, s.IsMutable, s.IsUserMutable, CloneType(s.Type), CloneAttributes(s.Attributes)),
        _ => new Field(Tok(f.tok), f.Name, f.HasStaticKeyword, f.IsGhost, f.IsMutable, f.IsUserMutable, CloneType(f.Type), CloneAttributes(f.Attributes))
      };
    }

    public virtual Function CloneFunction(Function f, string newName = null) {
      var tps = f.TypeArgs.ConvertAll(CloneTypeParam);
      var formals = f.Formals.ConvertAll(CloneFormal);
      var req = f.Req.ConvertAll(CloneAttributedExpr);
      var reads = f.Reads.ConvertAll(CloneFrameExpr);
      var decreases = CloneSpecExpr(f.Decreases);
      var ens = f.Ens.ConvertAll(CloneAttributedExpr);
      Expression body;
      body = CloneExpr(f.Body);

      if (newName == null) {
        newName = f.Name;
      }

      if (f is Predicate) {
        return new Predicate(Tok(f.tok), newName, f.HasStaticKeyword, f.IsGhost, tps, formals,
          req, reads, ens, decreases, body, Predicate.BodyOriginKind.OriginalOrInherited, CloneAttributes(f.Attributes), null);
      } else if (f is LeastPredicate) {
        return new LeastPredicate(Tok(f.tok), newName, f.HasStaticKeyword, ((LeastPredicate)f).TypeOfK, tps, formals,
          req, reads, ens, body, CloneAttributes(f.Attributes), null);
      } else if (f is GreatestPredicate) {
        return new GreatestPredicate(Tok(f.tok), newName, f.HasStaticKeyword, ((GreatestPredicate)f).TypeOfK, tps, formals,
          req, reads, ens, body, CloneAttributes(f.Attributes), null);
      } else if (f is TwoStatePredicate) {
        return new TwoStatePredicate(Tok(f.tok), newName, f.HasStaticKeyword, tps, formals,
          req, reads, ens, decreases, body, CloneAttributes(f.Attributes), null);
      } else if (f is TwoStateFunction) {
        return new TwoStateFunction(Tok(f.tok), newName, f.HasStaticKeyword, tps, formals, f.Result == null ? null : CloneFormal(f.Result), CloneType(f.ResultType),
          req, reads, ens, decreases, body, CloneAttributes(f.Attributes), null);
      } else {
        return new Function(Tok(f.tok), newName, f.HasStaticKeyword, f.IsGhost, tps, formals, f.Result == null ? null : CloneFormal(f.Result), CloneType(f.ResultType),
          req, reads, ens, decreases, body, CloneAttributes(f.Attributes), null);
      }
    }

    public virtual Method CloneMethod(Method m) {
      Contract.Requires(m != null);

      var tps = m.TypeArgs.ConvertAll(CloneTypeParam);
      var ins = m.Ins.ConvertAll(CloneFormal);
      var req = m.Req.ConvertAll(CloneAttributedExpr);
      var mod = CloneSpecFrameExpr(m.Mod);
      var decreases = CloneSpecExpr(m.Decreases);

      var ens = m.Ens.ConvertAll(CloneAttributedExpr);

      BlockStmt body = CloneMethodBody(m);

      if (m is Constructor) {
        return new Constructor(Tok(m.tok), m.Name, tps, ins,
          req, mod, ens, decreases, (DividedBlockStmt)body, CloneAttributes(m.Attributes), null);
      } else if (m is LeastLemma) {
        return new LeastLemma(Tok(m.tok), m.Name, m.HasStaticKeyword, ((LeastLemma)m).TypeOfK, tps, ins, m.Outs.ConvertAll(CloneFormal),
          req, mod, ens, decreases, body, CloneAttributes(m.Attributes), null);
      } else if (m is GreatestLemma) {
        return new GreatestLemma(Tok(m.tok), m.Name, m.HasStaticKeyword, ((GreatestLemma)m).TypeOfK, tps, ins, m.Outs.ConvertAll(CloneFormal),
          req, mod, ens, decreases, body, CloneAttributes(m.Attributes), null);
      } else if (m is Lemma) {
        return new Lemma(Tok(m.tok), m.Name, m.HasStaticKeyword, tps, ins, m.Outs.ConvertAll(CloneFormal),
          req, mod, ens, decreases, body, CloneAttributes(m.Attributes), null);
      } else if (m is TwoStateLemma) {
        var two = (TwoStateLemma)m;
        return new TwoStateLemma(Tok(m.tok), m.Name, m.HasStaticKeyword, tps, ins, m.Outs.ConvertAll(CloneFormal),
          req, mod, ens, decreases, body, CloneAttributes(m.Attributes), null);
      } else {
        return new Method(Tok(m.tok), m.Name, m.HasStaticKeyword, m.IsGhost, tps, ins, m.Outs.ConvertAll(CloneFormal),
          req, mod, ens, decreases, body, CloneAttributes(m.Attributes), null);
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

    private HashSet<AliasModuleDecl> extraProvides = new HashSet<AliasModuleDecl>();

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
        if (import == null)
          continue;

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

      basem.TopLevelDecls.RemoveAll(t =>
      {
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

    public override MemberDecl CloneMember(MemberDecl member) {
      var basem = base.CloneMember(member);
      reverseMap.Add(basem, member);
      return basem;
    }

  }

  /// <summary>
  /// This cloner is used during the creation of a module signature for a method facade.
  /// It does not clone method bodies, and it copies module signatures.
  /// </summary>
  class ClonerButDropMethodBodies : DeepModuleSignatureCloner
  {
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

    public override BlockStmt CloneBlockStmt(BlockStmt stmt) {
      return null;
    }
  }



  /// <summary>
  /// This cloner is used to clone a module into a _Compile module.  This is different from
  /// the standard cloner in the following ways:
  /// * "match" statements and "match" expressions obtain their original form, which may include
  ///   nested patterns.  The resolver will turn these into nested "match" constructs with simple
  ///   patterns.
  /// * The various module-signature fields of modules are set to whatever they were in the original.
  /// * To get the .RefinementBase, it redirects using the given mapping
  /// </summary>
  class CompilationCloner : DeepModuleSignatureCloner
  {
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

    public override Statement CloneStmt(Statement stmt) {
      var s = stmt as MatchStmt;
      if (s != null && s.OrigUnresolved != null) {
        return CloneStmt(s.OrigUnresolved);
      }
      return base.CloneStmt(stmt);
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

  /// <summary>
  /// Subclass of Cloner that collects some common functionality between ExtremeLemmaSpecificationSubstituter and
  /// ExtremeLemmaBodyCloner.
  /// </summary>
  abstract class ExtremeCloner : Cloner
  {
    protected readonly Expression k;
    protected readonly ErrorReporter reporter;
    protected readonly string suffix;
    protected ExtremeCloner(Expression k, ErrorReporter reporter)
    {
      Contract.Requires(k != null);
      Contract.Requires(reporter != null);
      this.k = k;
      this.reporter = reporter;
      this.suffix = string.Format("#[{0}]", Printer.ExprToString(k));
    }
    protected Expression CloneCallAndAddK(ApplySuffix e) {
      Contract.Requires(e != null);
      Contract.Requires(e.Resolved is FunctionCallExpr && ((FunctionCallExpr)e.Resolved).Function is ExtremePredicate);
      Contract.Requires(e.Lhs is NameSegment || e.Lhs is ExprDotName);
      Expression lhs;
      string name;
      var ns = e.Lhs as NameSegment;
      if (ns != null) {
        name = ns.Name;
        lhs = new NameSegment(Tok(ns.tok), name + "#", ns.OptTypeArguments == null ? null : ns.OptTypeArguments.ConvertAll(CloneType));
      } else {
        var edn = (ExprDotName)e.Lhs;
        name = edn.SuffixName;
        lhs = new ExprDotName(Tok(edn.tok), CloneExpr(edn.Lhs), name + "#", edn.OptTypeArguments == null ? null : edn.OptTypeArguments.ConvertAll(CloneType));
      }
      var args = new List<ActualBinding>();
      args.Add(new ActualBinding(null, k));
      foreach (var arg in e.Bindings.ArgumentBindings) {
        args.Add(CloneActualBinding(arg));
      }
      var apply = new ApplySuffix(Tok(e.tok), e.AtTok == null ? null : Tok(e.AtTok), lhs, args);
      reporter.Info(MessageSource.Cloner, e.tok, name + suffix);
      return apply;
    }
    protected Expression CloneCallAndAddK(FunctionCallExpr e) {
      Contract.Requires(e != null);
      Contract.Requires(e.Function is ExtremePredicate);
      var receiver = CloneExpr(e.Receiver);
      var args = new List<ActualBinding>();
      args.Add(new ActualBinding(null, k));
      foreach (var binding in e.Bindings.ArgumentBindings) {
        args.Add(CloneActualBinding(binding));
      }
      var fexp = new FunctionCallExpr(Tok(e.tok), e.Name + "#", receiver, e.OpenParen, args, e.AtLabel);
      reporter.Info(MessageSource.Cloner, e.tok, e.Name + suffix);
      return fexp;
    }
  }

  /// <summary>
  /// The ExtremeLemmaSpecificationSubstituter clones the precondition (or postcondition) declared
  /// on a least (resp. greatest) lemma, but replaces the calls and equalities in "coConclusions"
  /// with corresponding prefix versions.  The resulting expression is then appropriate to be a
  /// precondition (resp. postcondition) of the least (resp. greatest) lemma's corresponding prefix lemma.
  /// It is assumed that the source expression has been resolved.  Note, the "k" given to the constructor
  /// is not cloned with each use; it is simply used as is.
  /// The resulting expression needs to be resolved by the caller.
  /// </summary>
  class ExtremeLemmaSpecificationSubstituter : ExtremeCloner
  {
    readonly bool isCoContext;
    readonly ISet<Expression> friendlyCalls;
    public ExtremeLemmaSpecificationSubstituter(ISet<Expression> friendlyCalls, Expression k, ErrorReporter reporter, bool isCoContext)
      : base(k, reporter)
    {
      Contract.Requires(friendlyCalls != null);
      Contract.Requires(k != null);
      Contract.Requires(reporter != null);
      this.isCoContext = isCoContext;
      this.friendlyCalls = friendlyCalls;
    }
    public override Expression CloneExpr(Expression expr) {
      if (expr is NameSegment || expr is ExprDotName) {
        // make sure to clone any user-supplied type-parameter instantiations
        return base.CloneExpr(expr);
      } else if (expr is ApplySuffix) {
        var e = (ApplySuffix)expr;
        var r = e.Resolved as FunctionCallExpr;
        if (r != null && friendlyCalls.Contains(r)) {
          return CloneCallAndAddK(e);
        }
      } else if (expr is SuffixExpr) {
        // make sure to clone any user-supplied type-parameter instantiations
        return base.CloneExpr(expr);
      } else if (expr is ConcreteSyntaxExpression) {
        var e = (ConcreteSyntaxExpression)expr;
        // Note, the ExtremeLemmaSpecificationSubstituter is an unusual cloner in that it operates on
        // resolved expressions.  Hence, we bypass the syntactic parts here, except for the ones
        // checked above.
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
  /// The task of the ExtremeLemmaBodyCloner is to fill in the implicit _k-1 arguments in recursive least/greatest lemma calls
  /// and in calls to the focal predicates.
  /// The source statement and the given "k" are assumed to have been resolved.
  /// </summary>
  class ExtremeLemmaBodyCloner : ExtremeCloner
  {
    readonly ExtremeLemma context;
    readonly ISet<ExtremePredicate> focalPredicates;
    public ExtremeLemmaBodyCloner(ExtremeLemma context, Expression k, ISet<ExtremePredicate> focalPredicates, ErrorReporter reporter)
      : base(k, reporter)
    {
      Contract.Requires(context != null);
      Contract.Requires(k != null);
      Contract.Requires(reporter != null);
      this.context = context;
      this.focalPredicates = focalPredicates;
    }
    public override Statement CloneStmt(Statement stmt) {
      if (stmt is ConcreteSyntaxStatement) {
        var s = (ConcreteSyntaxStatement)stmt;
        return CloneStmt(s.ResolvedStatement);
      } else {
        return base.CloneStmt(stmt);
      }
    }

    public override Expression CloneExpr(Expression expr) {
      if (DafnyOptions.O.RewriteFocalPredicates) {
        if (expr is FunctionCallExpr) {
          var e = (FunctionCallExpr) expr;
#if DEBUG_PRINT
          if (e.Function.Name.EndsWith("#") && Contract.Exists(focalPredicates, p => e.Function.Name == p.Name + "#")) {
            Console.WriteLine("{0}({1},{2}): DEBUG: Possible opportunity to rely on new rewrite: {3}", e.tok.filename, e.tok.line, e.tok.col, Printer.ExprToString(e));
          }
#endif
          // Note, we don't actually ever get here, because all calls will have been parsed as ApplySuffix.
          // However, if something changes in the future (for example, some rewrite that changing an ApplySuffix
          // to its resolved FunctionCallExpr), then we do want this code, so with the hope of preventing
          // some error in the future, this case is included.  (Of course, it is currently completely untested!)
          var f = e.Function as ExtremePredicate;
          if (f != null && focalPredicates.Contains(f)) {
#if DEBUG_PRINT
            var r = CloneCallAndAddK(e);
            Console.WriteLine("{0}({1},{2}): DEBUG: Rewrote extreme predicate into prefix predicate: {3}", e.tok.filename, e.tok.line, e.tok.col, Printer.ExprToString(r));
            return r;
#else
            return CloneCallAndAddK(e);
#endif
          }
        } else if (expr is StaticReceiverExpr ee) {
          return new StaticReceiverExpr(Tok(ee.tok), ee.Type, ee.IsImplicit);
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
              var f = fce.Function as ExtremePredicate;
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
        if (mse != null && mse.Member is ExtremeLemma && ModuleDefinition.InSameSCC(context, (ExtremeLemma)mse.Member)) {
          // we're looking at a recursive call to an extreme lemma
          Contract.Assert(apply.Lhs is NameSegment || apply.Lhs is ExprDotName);  // this is the only way a call statement can have been parsed
          // clone "apply.Lhs", changing the least/greatest lemma to the prefix lemma; then clone "apply", adding in the extra argument
          Expression lhsClone;
          if (apply.Lhs is NameSegment) {
            var lhs = (NameSegment)apply.Lhs;
            lhsClone = new NameSegment(Tok(lhs.tok), lhs.Name + "#", lhs.OptTypeArguments == null ? null : lhs.OptTypeArguments.ConvertAll(CloneType));
          } else {
            var lhs = (ExprDotName)apply.Lhs;
            lhsClone = new ExprDotName(Tok(lhs.tok), CloneExpr(lhs.Lhs), lhs.SuffixName + "#", lhs.OptTypeArguments == null ? null : lhs.OptTypeArguments.ConvertAll(CloneType));
          }
          var args = new List<ActualBinding>();
          args.Add(new ActualBinding(null, k));
          apply.Bindings.ArgumentBindings.ForEach(arg => args.Add(CloneActualBinding(arg)));
          var applyClone = new ApplySuffix(Tok(apply.tok), apply.AtTok == null ? null : Tok(apply.AtTok), lhsClone, args);
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
      }

      return new_t;
    }

    public override CasePattern<VT> CloneCasePattern<VT>(CasePattern<VT> pat) {
      if (pat.Var != null) {
        var newPat = new CasePattern<VT>(pat.tok, CloneIVariable(pat.Var));
        newPat.AssembleExpr(null);
        return newPat;
      } else {
        var newArgs = pat.Arguments == null ? null : pat.Arguments.ConvertAll(CloneCasePattern);
        var patE = (DatatypeValue)pat.Expr;
        var newPat = new CasePattern<VT>(pat.tok, pat.Id, newArgs);
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
