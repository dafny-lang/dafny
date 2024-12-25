// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

using System;
using System.Collections.Generic;
using System.Numerics;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Xml;

namespace Microsoft.Dafny {
  interface ICloneable<out T> {
    T Clone(Cloner cloner);
  }

  public class Cloner {
    public bool CloneResolvedFields { get; }
    private readonly Dictionary<Statement, Statement> statementClones = new();
    private readonly Dictionary<IVariable, IVariable> clones = new();
    private readonly Dictionary<MemberDecl, MemberDecl> memberClones = new();
    private readonly Dictionary<TopLevelDecl, TopLevelDecl> typeParameterClones = new();
    public bool CloneLiteralModuleDefinition { get; }

    public void AddStatementClone(Statement original, Statement clone) {
      statementClones.Add(original, clone);
    }

    public TopLevelDecl GetCloneIfAvailable(TopLevelDecl topLevelDecl) {
      return typeParameterClones.GetOrDefault(topLevelDecl, () => topLevelDecl);
    }

    public Cloner(bool cloneLiteralModuleDefinition = false, bool cloneResolvedFields = false) {
      this.CloneLiteralModuleDefinition = cloneLiteralModuleDefinition;
      CloneResolvedFields = cloneResolvedFields;
    }

    public virtual ModuleDefinition CloneModuleDefinition(ModuleDefinition m, ModuleDefinition newParent) {
      if (m is DefaultModuleDefinition defaultModuleDefinition) {
        var result = new DefaultModuleDefinition(this, defaultModuleDefinition) {
          EnclosingModule = newParent
        };
        return result;
      }

      return new ModuleDefinition(this, m) {
        EnclosingModule = newParent
      };
    }

    public virtual ModuleDefinition CloneModuleDefinition(ModuleDefinition m, ModuleDefinition newParent, Name name) {
      if (m is DefaultModuleDefinition defaultModuleDefinition) {
        var result = new DefaultModuleDefinition(this, defaultModuleDefinition) {
          EnclosingModule = newParent
        };
        return result;
      }

      return new ModuleDefinition(this, m, name) {
        EnclosingModule = newParent
      };
    }

    public virtual TopLevelDecl CloneDeclaration(TopLevelDecl d, ModuleDefinition newParent) {
      Contract.Requires(d != null);
      Contract.Requires(newParent != null);

      if (d is AbstractTypeDecl) {
        var dd = (AbstractTypeDecl)d;
        return new AbstractTypeDecl(Origin(dd.Origin), dd.NameNode.Clone(this), newParent,
          CloneTPChar(dd.Characteristics), dd.TypeArgs.ConvertAll(CloneTypeParam),
          dd.ParentTraits.ConvertAll(CloneType),
          dd.Members.ConvertAll(d => CloneMember(d, false)), CloneAttributes(dd.Attributes), dd.IsRefining);
      } else if (d is SubsetTypeDecl) {
        Contract.Assume(
          !(d is NonNullTypeDecl)); // don't clone the non-null type declaration; close the class, which will create a new non-null type declaration
        var dd = (SubsetTypeDecl)d;
        var tps = dd.TypeArgs.ConvertAll(CloneTypeParam);
        return new SubsetTypeDecl(Origin(dd.Origin), dd.NameNode.Clone(this), CloneTPChar(dd.Characteristics), tps,
          newParent, CloneBoundVar(dd.Var, false), CloneExpr(dd.Constraint), dd.WitnessKind, CloneExpr(dd.Witness),
          CloneAttributes(dd.Attributes));
      } else if (d is TypeSynonymDecl) {
        var dd = (TypeSynonymDecl)d;
        var tps = dd.TypeArgs.ConvertAll(CloneTypeParam);
        return new TypeSynonymDecl(Origin(dd.Origin), dd.NameNode.Clone(this), CloneTPChar(dd.Characteristics), tps,
          newParent, CloneType(dd.Rhs), CloneAttributes(dd.Attributes));
      } else if (d is NewtypeDecl) {
        var dd = (NewtypeDecl)d;
        if (dd.Var == null) {
          return new NewtypeDecl(Origin(dd.Origin), dd.NameNode.Clone(this), dd.TypeArgs.ConvertAll(CloneTypeParam), newParent,
            CloneType(dd.BaseType), dd.WitnessKind, CloneExpr(dd.Witness),
            dd.ParentTraits.ConvertAll(CloneType),
            dd.Members.ConvertAll(d => CloneMember(d, false)), CloneAttributes(dd.Attributes), dd.IsRefining);
        } else {
          return new NewtypeDecl(Origin(dd.Origin), dd.NameNode.Clone(this), dd.TypeArgs.ConvertAll(CloneTypeParam), newParent,
            CloneBoundVar(dd.Var, false), CloneExpr(dd.Constraint), dd.WitnessKind, CloneExpr(dd.Witness),
            dd.ParentTraits.ConvertAll(CloneType),
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
        var dt = new IndDatatypeDecl(Origin(dd.Origin), dd.NameNode.Clone(this), newParent, tps, ctors,
          dd.ParentTraits.ConvertAll(CloneType),
          dd.Members.ConvertAll(d => CloneMember(d, false)), CloneAttributes(dd.Attributes), dd.IsRefining);
        return dt;
      } else if (d is CoDatatypeDecl) {
        var dd = (CoDatatypeDecl)d;
        var tps = dd.TypeArgs.ConvertAll(CloneTypeParam);
        var ctors = dd.Ctors.ConvertAll(CloneCtor);
        var dt = new CoDatatypeDecl(Origin(dd.Origin), dd.NameNode.Clone(this), newParent, tps, ctors,
          dd.ParentTraits.ConvertAll(CloneType),
          dd.Members.ConvertAll(d => CloneMember(d, false)), CloneAttributes(dd.Attributes), dd.IsRefining);
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
        var iter = new IteratorDecl(Origin(dd.Origin), dd.NameNode.Clone(this), newParent,
          tps, ins, outs, reads, mod, decr,
          req, ens, yreq, yens,
          body, CloneAttributes(dd.Attributes), dd.SignatureEllipsis);
        return iter;
      } else if (d is TraitDecl) {
        var dd = (TraitDecl)d;
        var tps = dd.TypeArgs.ConvertAll(CloneTypeParam);
        var mm = dd.Members.ConvertAll(member => CloneMember(member, false));
        var cl = new TraitDecl(Origin(dd.Origin), dd.NameNode.Clone(this), newParent, tps, mm,
          CloneAttributes(dd.Attributes), dd.IsRefining, dd.ParentTraits.ConvertAll(CloneType));
        return cl;
      } else if (d is DefaultClassDecl) {
        var dd = (DefaultClassDecl)d;
        var tps = dd.TypeArgs.ConvertAll(CloneTypeParam);
        var mm = dd.Members.ConvertAll(member => CloneMember(member, false));
        return new DefaultClassDecl(newParent, mm);
      } else if (d is ClassDecl) {
        var dd = (ClassDecl)d;
        var tps = dd.TypeArgs.ConvertAll(CloneTypeParam);
        var mm = dd.Members.ConvertAll(member => CloneMember(member, false));
        return new ClassDecl(Origin(dd.Origin), dd.NameNode.Clone(this), newParent, tps, mm,
          CloneAttributes(dd.Attributes), dd.IsRefining, dd.ParentTraits.ConvertAll(CloneType));
      } else if (d is ModuleDecl) {
        if (d is LiteralModuleDecl moduleDecl) {
          return new LiteralModuleDecl(this, moduleDecl, newParent);
        } else if (d is AliasModuleDecl) {
          var a = (AliasModuleDecl)d;
          return new AliasModuleDecl(this, a, newParent);
        } else if (d is AbstractModuleDecl) {
          var a = (AbstractModuleDecl)d;
          return new AbstractModuleDecl(this, a, newParent);
        } else if (d is ModuleExportDecl) {
          var a = (ModuleExportDecl)d;
          return new ModuleExportDecl(this, a, newParent);
        } else {
          Contract.Assert(false); // unexpected declaration
          return null; // to please compiler
        }
      } else {
        Contract.Assert(false); // unexpected declaration
        return null; // to please compiler
      }
    }

    public TypeParameter.TypeParameterCharacteristics CloneTPChar(
      TypeParameter.TypeParameterCharacteristics characteristics) {
      TypeParameter.EqualitySupportValue eqSupport;
      if (characteristics.EqualitySupport == TypeParameter.EqualitySupportValue.InferredRequired) {
        eqSupport = TypeParameter.EqualitySupportValue.Unspecified;
      } else {
        eqSupport = characteristics.EqualitySupport;
      }

      return new TypeParameter.TypeParameterCharacteristics(eqSupport, characteristics.AutoInit,
        characteristics.ContainsNoReferenceTypes);
    }

    public DatatypeCtor CloneCtor(DatatypeCtor ct) {
      return new DatatypeCtor(Origin(ct.Origin), ct.NameNode.Clone(this), ct.IsGhost,
        ct.Formals.ConvertAll(bv => CloneFormal(bv, false)), CloneAttributes(ct.Attributes));
    }

    public TypeParameter CloneTypeParam(TypeParameter tp) {
      return (TypeParameter)typeParameterClones.GetOrCreate(tp,
        () => new TypeParameter(Origin(tp.Origin), tp.NameNode.Clone(this), tp.VarianceSyntax,
          CloneTPChar(tp.Characteristics), tp.TypeBounds.ConvertAll(CloneType)));
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
        return new SetType(tt.Finite, tt.HasTypeArg() ? CloneType(tt.Arg) : null);
      } else if (t is SeqType) {
        var tt = (SeqType)t;
        return new SeqType(tt.HasTypeArg() ? CloneType(tt.Arg) : null);
      } else if (t is MultiSetType) {
        var tt = (MultiSetType)t;
        return new MultiSetType(tt.HasTypeArg() ? CloneType(tt.Arg) : null);
      } else if (t is MapType mapType) {
        return new MapType(this, mapType);
      } else if (t is ArrowType) {
        var tt = (ArrowType)t;
        return new ArrowType(Origin(tt.Tok), tt.Args.ConvertAll(CloneType), CloneType(tt.Result));
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
      } else if (t is TypeRefinementWrapper typeRefinementWrapper) {
        // don't bother keeping TypeRefinementWrapper wrappers
        return CloneType(typeRefinementWrapper.T);
      } else {
        Contract.Assert(false); // unexpected type (e.g., no other type proxies are expected at this time)
        return null; // to please compiler
      }
    }

    public virtual Formal CloneFormal(Formal formal, bool isReference) {
      return (Formal)clones.GetOrCreate(formal, () => isReference
       ? formal
       : new Formal(Origin(formal.Tok), new Name(this, formal.NameNode), CloneType(formal.Type), formal.InParam, formal.IsGhost,
         CloneExpr(formal.DefaultValue), CloneAttributes(formal.Attributes),
         formal.IsOld, formal.IsNameOnly, formal.IsOlder, formal.NameForCompilation) {
         Origin = formal.Origin,
         IsTypeExplicit = formal.IsTypeExplicit
       });
    }

    public virtual BoundVar CloneBoundVar(BoundVar bv, bool isReference) {
      return (BoundVar)clones.GetOrCreate(bv, () => {
        if (isReference) {
          return bv;
        }

        var bvNew = new BoundVar(Origin(bv.Tok), new Name(this, bv.NameNode), CloneType(bv.SyntacticType));
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
      } else if (attrs is UserSuppliedAttributes usa) {
        return new UserSuppliedAttributes(Origin(usa.Tok), Origin(usa.OpenBrace), Origin(usa.CloseBrace),
          attrs.Args.ConvertAll(CloneExpr), CloneAttributes(attrs.Prev)) {
          Origin = Origin(usa.Origin)
        };
      } else if (attrs is UserSuppliedAtAttribute usaa) {
        var arg = CloneExpr(usaa.Arg);
        if (usaa.Arg.Type != null) { // The attribute has already been expanded
          arg.Type = usaa.Arg.Type;
          arg.PreType = usaa.Arg.PreType;
        }
        return new UserSuppliedAtAttribute(Origin(usaa.Tok), arg, CloneAttributes(usaa.Prev)) {
          Origin = Origin(usaa.Origin),
          Builtin = usaa.Builtin
        };
      } else {
        return new Attributes(attrs.Name, attrs.Args.ConvertAll(CloneExpr), CloneAttributes(attrs.Prev)) {
          Origin = Origin(attrs.Origin)
        };
      }
    }

    public AttributedExpression CloneAttributedExpr(AttributedExpression expr) {
      var mfe = new AttributedExpression(CloneExpr(expr.E),
        expr.Label == null ? null : new AssertLabel(Origin(expr.Label.Tok), expr.Label.Name),
        CloneAttributes(expr.Attributes));
      mfe.Attributes = CloneAttributes(expr.Attributes);
      return mfe;
    }

    public virtual ActualBinding CloneActualBinding(ActualBinding binding) {
      return new ActualBinding(binding.FormalParameterName == null ? null : Origin(binding.FormalParameterName),
        CloneExpr(binding.Actual));
    }

    public virtual Expression CloneExpr(Expression expr) {
      if (expr == null) {
        return null;
      }

      if (expr is ICloneable<Expression> cloneableExpression) {
        return cloneableExpression.Clone(this);
      }

      throw new Exception($"No clone implementation found for {expr.GetType()}"); // unexpected expression
    }

    public MatchCaseExpr CloneMatchCaseExpr(MatchCaseExpr c) {
      Contract.Requires(c != null);
      Contract.Requires(c.Arguments != null);
      return new MatchCaseExpr(Origin(c.Tok), c.Ctor, c.FromBoundVar,
        c.Arguments.ConvertAll(bv => CloneBoundVar(bv, false)), CloneExpr(c.Body), CloneAttributes(c.Attributes));
    }

    public NestedMatchCaseExpr CloneNestedMatchCaseExpr(NestedMatchCaseExpr c) {
      Contract.Requires(c != null);
      return new NestedMatchCaseExpr(Origin(c.Tok), CloneExtendedPattern(c.Pat), CloneExpr(c.Body),
        CloneAttributes(c.Attributes));
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
      if (rhs is ICloneable<AssignmentRhs> cloneable) {
        return cloneable.Clone(this);
      }

      throw new Exception($"No clone implementation found for {rhs.GetType()}"); // unexpected RHS
    }

    public virtual BlockStmt CloneBlockStmt(BlockStmt stmt) {
      Contract.Requires(
        !(stmt is DividedBlockStmt)); // for blocks that may be DividedBlockStmt's, call CloneDividedBlockStmt instead
      if (stmt == null) {
        return null;
      } else {
        return new BlockStmt(Origin(stmt.Origin), stmt.Body.ConvertAll(stmt1 => CloneStmt(stmt1, false)));
      }
    }

    public virtual DividedBlockStmt CloneDividedBlockStmt(DividedBlockStmt stmt) {
      if (stmt == null) {
        return null;
      } else {
        return new DividedBlockStmt(Origin(stmt.Origin), stmt.BodyInit.ConvertAll(stmt1 => CloneStmt(stmt1, false)),
          stmt.SeparatorTok == null ? null : Origin(stmt.SeparatorTok), stmt.BodyProper.ConvertAll(stmt1 => CloneStmt(stmt1, false)));
      }
    }

    public virtual Statement CloneStmt(Statement stmt, bool isReference) {
      if (stmt == null) {
        return null;
      }


      if (statementClones.TryGetValue(stmt, out var cachedResult)) {
        return cachedResult;
      }

      if (isReference) {
        return stmt;
      }

      if (stmt is ICloneable<Statement> cloneable) {
        var r = cloneable.Clone(this);
        // add labels to the cloned statement
        AddStmtLabels(r, stmt.Labels);
        r.Attributes = CloneAttributes(stmt.Attributes);

        return r;
      }

      Contract.Assert(false);
      throw new cce.UnreachableException(); // unexpected statement TODO, make all statements inherit from ICloneable.
    }

    public MatchCaseStmt CloneMatchCaseStmt(MatchCaseStmt c) {
      Contract.Requires(c != null);
      Contract.Assert(c.Arguments != null);
      return new MatchCaseStmt(Origin(c.Origin), c.Ctor, c.FromBoundVar,
        c.Arguments.ConvertAll(v => CloneBoundVar(v, false)),
        c.Body.ConvertAll(stmt => CloneStmt(stmt, false)), CloneAttributes(c.Attributes));
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
      return new NestedMatchCaseStmt(c.Tok, CloneExtendedPattern(c.Pat), c.Body.ConvertAll(stmt => CloneStmt(stmt, false)),
        CloneAttributes(c.Attributes));
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
          s.Labels = new LList<Label>(new Label(Origin(node.Data.Tok), node.Data.Name), s.Labels);
        }
      }
    }

    public GuardedAlternative CloneGuardedAlternative(GuardedAlternative alt) {
      return new GuardedAlternative(Origin(alt.Tok), alt.IsBindingGuard, CloneExpr(alt.Guard),
        alt.Body.ConvertAll(stmt => CloneStmt(stmt, false)), CloneAttributes(alt.Attributes));
    }

    public virtual Field CloneField(Field f) {
      Contract.Requires(f != null);
      return f switch {
        ConstantField c => new ConstantField(Origin(c.Origin), c.NameNode.Clone(this), CloneExpr(c.Rhs),
          c.HasStaticKeyword, c.IsGhost, c.IsOpaque, CloneType(c.Type), CloneAttributes(c.Attributes)),
        // We don't expect a SpecialField to ever be cloned. However, it can happen for malformed programs, for example if
        // an iterator in a refined module is replaced by a class in the refining module.
        SpecialField s => new SpecialField(Origin(s.Origin), s.Name, s.SpecialId, s.IdParam, s.IsGhost, s.IsMutable,
          s.IsUserMutable, CloneType(s.Type), CloneAttributes(s.Attributes)),
        _ => new Field(Origin(f.Origin), f.NameNode.Clone(this), f.HasStaticKeyword, f.IsGhost, f.IsMutable,
          f.IsUserMutable, CloneType(f.Type), CloneAttributes(f.Attributes))
      };
    }

    public virtual Function CloneFunction(Function f, string newName = null) {
      var tps = f.TypeArgs.ConvertAll(CloneTypeParam);
      var formals = f.Ins.ConvertAll(p => CloneFormal(p, false));
      var result = f.Result != null ? CloneFormal(f.Result, false) : null;
      var req = f.Req.ConvertAll(CloneAttributedExpr);
      var reads = CloneSpecFrameExpr(f.Reads);
      var decreases = CloneSpecExpr(f.Decreases);
      var ens = f.Ens.ConvertAll(CloneAttributedExpr);
      Expression body = CloneExpr(f.Body);
      BlockStmt byMethodBody = CloneBlockStmt(f.ByMethodBody);

      if (newName == null) {
        newName = f.Name;
      }

      var newNameNode = new Name(Origin(f.NameNode.Origin), newName);

      if (f is Predicate) {
        return new Predicate(Origin(f.Origin), newNameNode, f.HasStaticKeyword, f.IsGhost, f.IsOpaque, tps, formals,
          result,
          req, reads, ens, decreases, body, Predicate.BodyOriginKind.OriginalOrInherited,
          f.ByMethodTok == null ? null : Origin(f.ByMethodTok), byMethodBody,
          CloneAttributes(f.Attributes), null);
      } else if (f is LeastPredicate) {
        return new LeastPredicate(Origin(f.Origin), newNameNode, f.HasStaticKeyword, f.IsOpaque,
          ((LeastPredicate)f).TypeOfK, tps, formals, result,
          req, reads, ens, body, CloneAttributes(f.Attributes), null);
      } else if (f is GreatestPredicate greatestPredicate) {
        return new GreatestPredicate(Origin(f.Origin), newNameNode, f.HasStaticKeyword, f.IsOpaque,
          ((GreatestPredicate)f).TypeOfK, tps, formals, result,
          req, reads, ens, body, CloneAttributes(f.Attributes), null);
      } else if (f is TwoStatePredicate) {
        return new TwoStatePredicate(Origin(f.Origin), newNameNode, f.HasStaticKeyword, f.IsOpaque, tps, formals,
          result,
          req, reads, ens, decreases, body, CloneAttributes(f.Attributes), null);
      } else if (f is TwoStateFunction) {
        return new TwoStateFunction(Origin(f.Origin), newNameNode, f.HasStaticKeyword, f.IsOpaque, tps, formals,
          result, CloneType(f.ResultType),
          req, reads, ens, decreases, body, CloneAttributes(f.Attributes), null);
      } else {
        return new Function(Origin(f.Origin), newNameNode, f.HasStaticKeyword, f.IsGhost, f.IsOpaque, tps, formals,
          result, CloneType(f.ResultType),
          req, reads, ens, decreases, body, f.ByMethodTok == null ? null : Origin(f.ByMethodTok), byMethodBody,
          CloneAttributes(f.Attributes), null);
      }
    }

    public virtual Method CloneMethod(Method m) {
      Contract.Requires(m != null);
      return m switch {
        Constructor constructor => new Constructor(this, constructor),
        LeastLemma leastLemma => new LeastLemma(this, leastLemma),
        GreatestLemma greatestLemma => new GreatestLemma(this, greatestLemma),
        Lemma lemma => new Lemma(this, lemma),
        TwoStateLemma lemma => new TwoStateLemma(this, lemma),
        _ => new Method(this, m)
      };
    }

    public virtual BlockStmt CloneMethodBody(Method m) {
      if (m.Body is DividedBlockStmt) {
        return CloneDividedBlockStmt((DividedBlockStmt)m.Body);
      } else {
        return CloneBlockStmt(m.Body);
      }
    }

    public virtual IOrigin Origin(IOrigin tok) {
      if (tok == null) {
        return null;
      }

      Contract.Requires(tok != null);
      return tok;
    }

    public virtual AttributedToken AttributedTok(AttributedToken tok) {
      if (tok == null) {
        return null;
      }

      return new AttributedToken(Origin(tok.Token), CloneAttributes(tok.Attrs));
    }
  }

  public class ClonerKeepParensExpressions : Cloner {
    public override Expression CloneExpr(Expression expr) {
      if (expr is ParensExpression parensExpression) {
        return new ParensExpression(Origin(parensExpression.Tok), CloneExpr(parensExpression.E));
      }

      return base.CloneExpr(expr);
    }
  }

  /// <summary>
  /// This cloner copies the origin module signatures to their cloned declarations
  /// </summary>
  class DeepModuleSignatureCloner : Cloner {
    public DeepModuleSignatureCloner(bool cloneResolvedFields = false) : base(false, cloneResolvedFields) {
    }

    public override TopLevelDecl CloneDeclaration(TopLevelDecl d, ModuleDefinition newParent) {
      var dd = base.CloneDeclaration(d, newParent);
      if (d is ModuleDecl) {
        ((ModuleDecl)dd).Signature = ((ModuleDecl)d).Signature;
        if (d is AbstractModuleDecl) {
          var sourcefacade = (AbstractModuleDecl)d;

          ((AbstractModuleDecl)dd).OriginalSignature = sourcefacade.OriginalSignature;
          if (sourcefacade.QId.Root != null) {
            ((AbstractModuleDecl)dd).QId.Root = (ModuleDecl)CloneDeclaration(sourcefacade.QId.Root, newParent);
          }
        } else if (d is AliasModuleDecl) {
          var sourcealias = (AliasModuleDecl)d;

          if (sourcealias.TargetQId.Root != null) {
            ((AliasModuleDecl)dd).TargetQId.Root =
              (ModuleDecl)CloneDeclaration(sourcealias.TargetQId.Root, newParent);
          }
        }
      }

      return dd;
    }
  }


  /// <summary>
  /// This cloner is used during the creation of a module signature for a method facade.
  /// It does not clone method bodies, and it copies module signatures.
  /// </summary>
  class ClonerButDropMethodBodies : DeepModuleSignatureCloner {
    public ClonerButDropMethodBodies(bool cloneResolvedFields = false) : base(cloneResolvedFields) {
    }

    public override BlockStmt CloneBlockStmt(BlockStmt stmt) {
      return null;
    }
  }
}