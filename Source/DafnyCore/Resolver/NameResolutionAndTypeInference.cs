#define TI_DEBUG_PRINT
//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------
using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;
using System.Diagnostics.Contracts;
using System.IO;
using System.Reflection;
using JetBrains.Annotations;
using Microsoft.BaseTypes;
using Microsoft.Boogie;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Microsoft.Dafny.Plugins;
using static Microsoft.Dafny.ErrorDetail;

namespace Microsoft.Dafny {
  public partial class Resolver {
    /// <summary>
    /// There are two rounds of name resolution + type inference. The "initialRound" parameter says which one to do.
    /// </summary>
    void ResolveNamesAndInferTypes(List<TopLevelDecl> declarations, bool initialRound) {
      foreach (TopLevelDecl topd in declarations) {
        Contract.Assert(topd != null);
        Contract.Assert(VisibleInScope(topd));
        Contract.Assert(AllTypeConstraints.Count == 0);
        Contract.Assert(currentClass == null);

        allTypeParameters.PushMarker();
        ResolveTypeParameters(topd.TypeArgs, !initialRound, topd);

        if (initialRound) {
          ResolveNamesAndInferTypesForOneDeclarationInitial(topd);
        } else {
          ResolveNamesAndInferTypesForOneDeclaration(topd);
        }

        allTypeParameters.PopMarker();

        Contract.Assert(AllTypeConstraints.Count == 0);
        Contract.Assert(currentClass == null);
      }
    }

    /// <summary>
    /// Assumes type parameters of "topd" have already been pushed.
    /// </summary>
    void ResolveNamesAndInferTypesForOneDeclarationInitial(TopLevelDecl topd) {
      if (topd is NewtypeDecl newtypeDecl) {
        // this check can be done only after it has been determined that the redirected types do not involve cycles
        AddXConstraint(newtypeDecl.tok, "NumericType", newtypeDecl.BaseType, "newtypes must be based on some numeric type (got {0})");
        // type check the constraint, if any
        if (newtypeDecl.Var != null) {
          Contract.Assert(object.ReferenceEquals(newtypeDecl.Var.Type, newtypeDecl.BaseType));  // follows from NewtypeDecl invariant
          Contract.Assert(newtypeDecl.Constraint != null);  // follows from NewtypeDecl invariant

          scope.PushMarker();
          scope.AllowInstance = false;
          var added = scope.Push(newtypeDecl.Var.Name, newtypeDecl.Var);
          Contract.Assert(added == Scope<IVariable>.PushResult.Success);
          ResolveExpression(newtypeDecl.Constraint, new ResolutionContext(new CodeContextWrapper(newtypeDecl, true), false));
          Contract.Assert(newtypeDecl.Constraint.Type != null);  // follows from postcondition of ResolveExpression
          ConstrainTypeExprBool(newtypeDecl.Constraint, "newtype constraint must be of type bool (instead got {0})");
          scope.PopMarker();
        }
        SolveAllTypeConstraints();

      } else if (topd is SubsetTypeDecl subsetTypeDecl) {
        // type check the constraint
        Contract.Assert(object.ReferenceEquals(subsetTypeDecl.Var.Type, subsetTypeDecl.Rhs)); // follows from SubsetTypeDecl invariant
        Contract.Assert(subsetTypeDecl.Constraint != null); // follows from SubsetTypeDecl invariant
        scope.PushMarker();
        scope.AllowInstance = false;
        var added = scope.Push(subsetTypeDecl.Var.Name, subsetTypeDecl.Var);
        Contract.Assert(added == Scope<IVariable>.PushResult.Success);
        ResolveExpression(subsetTypeDecl.Constraint, new ResolutionContext(new CodeContextWrapper(subsetTypeDecl, true), false));
        Contract.Assert(subsetTypeDecl.Constraint.Type != null); // follows from postcondition of ResolveExpression
        ConstrainTypeExprBool(subsetTypeDecl.Constraint, "subset-type constraint must be of type bool (instead got {0})");
        scope.PopMarker();
        SolveAllTypeConstraints();
      }

      if (topd is TopLevelDeclWithMembers cl) {
        ResolveClassMemberBodiesInitial(cl);
      }
    }

    void ResolveNamesAndInferTypesForOneDeclaration(TopLevelDecl topd) {
      if (topd is NewtypeDecl newtypeDecl) {
        if (newtypeDecl.Witness != null) {
          var codeContext = new CodeContextWrapper(newtypeDecl, newtypeDecl.WitnessKind == SubsetTypeDecl.WKind.Ghost);
          scope.PushMarker();
          scope.AllowInstance = false;
          ResolveExpression(newtypeDecl.Witness, new ResolutionContext(codeContext, false));
          scope.PopMarker();
          ConstrainSubtypeRelation(newtypeDecl.Var.Type, newtypeDecl.Witness.Type, newtypeDecl.Witness, "witness expression must have type '{0}' (got '{1}')", newtypeDecl.Var.Type, newtypeDecl.Witness.Type);
        }
        SolveAllTypeConstraints();

      } else if (topd is SubsetTypeDecl subsetTypeDecl) {
        if (subsetTypeDecl.Witness != null) {
          var codeContext = new CodeContextWrapper(subsetTypeDecl, subsetTypeDecl.WitnessKind == SubsetTypeDecl.WKind.Ghost);
          scope.PushMarker();
          scope.AllowInstance = false;
          ResolveExpression(subsetTypeDecl.Witness, new ResolutionContext(codeContext, false));
          scope.PopMarker();
          ConstrainSubtypeRelation(subsetTypeDecl.Var.Type, subsetTypeDecl.Witness.Type, subsetTypeDecl.Witness,
            "witness expression must have type '{0}' (got '{1}')", subsetTypeDecl.Var.Type, subsetTypeDecl.Witness.Type);
        }
        SolveAllTypeConstraints();

      } else if (topd is IteratorDecl iteratorDecl) {
        ResolveIterator(iteratorDecl);

      } else if (topd is DatatypeDecl dt) {
        // resolve any default parameters
        foreach (var ctor in dt.Ctors) {
          scope.PushMarker();
          scope.AllowInstance = false;
          ctor.Formals.ForEach(p => scope.Push(p.Name, p));
          ResolveParameterDefaultValues(ctor.Formals, ResolutionContext.FromCodeContext(dt));
          ResolveAttributes(ctor, new ResolutionContext(new NoContext(topd.EnclosingModuleDefinition), false), true);
          scope.PopMarker();
        }
      }

      if (topd is TopLevelDeclWithMembers cl) {
        ResolveClassMemberBodies(cl);
      }

      // resolve attributes
      scope.PushMarker();
      Contract.Assert(currentClass == null);
      scope.AllowInstance = false;
      if (topd is IteratorDecl iter) {
        iter.Ins.ForEach(p => scope.Push(p.Name, p));
      }
      ResolveAttributes(topd, new ResolutionContext(new NoContext(topd.EnclosingModuleDefinition), false), true);
      scope.PopMarker();
    }

    void EagerAddAssignableConstraint(IToken tok, Type lhs, Type rhs, string errMsgFormat) {
      Contract.Requires(tok != null);
      Contract.Requires(lhs != null);
      Contract.Requires(rhs != null);
      Contract.Requires(errMsgFormat != null);
      var lhsNormalized = lhs.Normalize();
      var rhsNormalized = rhs.Normalize();
      if (lhsNormalized is TypeProxy lhsProxy && !(rhsNormalized is TypeProxy)) {
        Contract.Assert(lhsProxy.T == null); // otherwise, lhs.Normalize() above would have kept on going
        AssignProxyAndHandleItsConstraints(lhsProxy, rhsNormalized, true);
      } else {
        AddAssignableConstraint(tok, lhs, rhs, errMsgFormat);
      }
    }
    public void AddAssignableConstraint(IToken tok, Type lhs, Type rhs, string errMsgFormat) {
      Contract.Requires(tok != null);
      Contract.Requires(lhs != null);
      Contract.Requires(rhs != null);
      Contract.Requires(errMsgFormat != null);
      AddXConstraint(tok, "Assignable", lhs, rhs, errMsgFormat);
    }
    private void AddXConstraint(IToken tok, string constraintName, Type type, string errMsgFormat) {
      Contract.Requires(tok != null);
      Contract.Requires(constraintName != null);
      Contract.Requires(type != null);
      Contract.Requires(errMsgFormat != null);
      var types = new Type[] { type };
      AllXConstraints.Add(new XConstraint(tok, constraintName, types, new TypeConstraint.ErrorMsgWithToken(tok, errMsgFormat, types)));
    }
    void AddAssignableConstraint(IToken tok, Type lhs, Type rhs, TypeConstraint.ErrorMsg errMsg) {
      Contract.Requires(tok != null);
      Contract.Requires(lhs != null);
      Contract.Requires(rhs != null);
      Contract.Requires(errMsg != null);
      AddXConstraint(tok, "Assignable", lhs, rhs, errMsg);
    }
    private void AddXConstraint(IToken tok, string constraintName, Type type, TypeConstraint.ErrorMsg errMsg) {
      Contract.Requires(tok != null);
      Contract.Requires(constraintName != null);
      Contract.Requires(type != null);
      Contract.Requires(errMsg != null);
      var types = new Type[] { type };
      AllXConstraints.Add(new XConstraint(tok, constraintName, types, errMsg));
    }
    private void AddXConstraint(IToken tok, string constraintName, Type type0, Type type1, string errMsgFormat) {
      Contract.Requires(tok != null);
      Contract.Requires(constraintName != null);
      Contract.Requires(type0 != null);
      Contract.Requires(type1 != null);
      Contract.Requires(errMsgFormat != null);
      var types = new Type[] { type0, type1 };
      AllXConstraints.Add(new XConstraint(tok, constraintName, types, new TypeConstraint.ErrorMsgWithToken(tok, errMsgFormat, types)));
    }
    private void AddXConstraint(IToken tok, string constraintName, Type type0, Type type1, TypeConstraint.ErrorMsg errMsg) {
      Contract.Requires(tok != null);
      Contract.Requires(constraintName != null);
      Contract.Requires(type0 != null);
      Contract.Requires(type1 != null);
      Contract.Requires(errMsg != null);
      var types = new Type[] { type0, type1 };
      AllXConstraints.Add(new XConstraint(tok, constraintName, types, errMsg));
    }
    private void AddXConstraint(IToken tok, string constraintName, Type type, Expression expr0, Expression expr1, string errMsgFormat) {
      Contract.Requires(tok != null);
      Contract.Requires(constraintName != null);
      Contract.Requires(type != null);
      Contract.Requires(expr0 != null);
      Contract.Requires(expr1 != null);
      Contract.Requires(errMsgFormat != null);
      var types = new Type[] { type };
      var exprs = new Expression[] { expr0, expr1 };
      AllXConstraints.Add(new XConstraintWithExprs(tok, constraintName, types, exprs, new TypeConstraint.ErrorMsgWithToken(tok, errMsgFormat, types)));
    }

    [System.Diagnostics.Conditional("TI_DEBUG_PRINT")]
    void PrintTypeConstraintState(int lbl) {
      if (!DafnyOptions.O.TypeInferenceDebug) {
        return;
      }
      Console.WriteLine("DEBUG: ---------- type constraints ---------- {0} {1}", lbl, lbl == 0 && currentMethod != null ? currentMethod.Name : "");
      foreach (var constraint in AllTypeConstraints) {
        var super = constraint.Super.Normalize();
        var sub = constraint.Sub.Normalize();
        Console.WriteLine("    {0} :> {1}", super is IntVarietiesSupertype ? "int-like" : super is RealVarietiesSupertype ? "real-like" : super.ToString(), sub);
      }
      foreach (var xc in AllXConstraints) {
        Console.WriteLine("    {0}", xc);
      }
      Console.WriteLine();
      if (lbl % 2 == 1) {
        Console.WriteLine("DEBUG: --------------------------------------");
      }
    }

    /// <summary>
    /// Attempts to fully solve all type constraints.
    /// Upon failure, reports errors.
    /// Clears all constraints.
    /// </summary>
    public void SolveAllTypeConstraints() {
      PrintTypeConstraintState(0);
      PartiallySolveTypeConstraints(true);
      PrintTypeConstraintState(1);
      foreach (var constraint in AllTypeConstraints) {
        if (Type.IsSupertype(constraint.Super, constraint.Sub)) {
          // unexpected condition -- PartiallySolveTypeConstraints is supposed to have continued until no more sub-typing constraints can be satisfied
          Contract.Assume(false, string.Format("DEBUG: Unexpectedly satisfied supertype relation ({0} :> {1}) |||| ", constraint.Super, constraint.Sub));
        } else {
          constraint.FlagAsError(this);
        }
      }
      foreach (var xc in AllXConstraints) {
        bool convertedIntoOtherTypeConstraints, moreXConstraints;
        if (xc.Confirm(this, true, out convertedIntoOtherTypeConstraints, out moreXConstraints)) {
          // unexpected condition -- PartiallySolveTypeConstraints is supposed to have continued until no more XConstraints were confirmable
          Contract.Assume(false, string.Format("DEBUG: Unexpectedly confirmed XConstraint: {0} |||| ", xc));
        } else if (xc.CouldBeAnything()) {
          // suppress the error message; it will later be flagged as an underspecified type
        } else {
          xc.errorMsg.FlagAsError(this);
        }
      }
      TypeConstraint.ReportErrors(this, reporter);
      AllTypeConstraints.Clear();
      AllXConstraints.Clear();
    }

    /// <summary>
    /// Adds type constraints for the expressions in the given attributes.
    ///
    /// If "solveConstraints" is "true", then the constraints are also solved. In this case, it is assumed on entry that there are no
    /// prior type constraints. That is, the only type constraints being solved for are the ones in the given attributes.
    /// </summary>
    public void ResolveAttributes(IAttributeBearingDeclaration attributeHost, ResolutionContext resolutionContext, bool solveConstraints = false) {
      Contract.Requires(resolutionContext != null);
      Contract.Requires(attributeHost != null);

      Contract.Assume(!solveConstraints || AllTypeConstraints.Count == 0);

      // order does not matter much for resolution, so resolve them in reverse order
      foreach (var attr in attributeHost.Attributes.AsEnumerable()) {
        if (attr is UserSuppliedAttributes) {
          var usa = (UserSuppliedAttributes)attr;
          usa.Recognized = IsRecognizedAttribute(usa, attributeHost);
        }
        if (attr.Args != null) {
          foreach (var arg in attr.Args) {
            Contract.Assert(arg != null);
            ResolveExpression(arg, resolutionContext);
          }
        }
      }

      if (solveConstraints) {
        SolveAllTypeConstraints();
      }
    }

    /// <summary>
    /// "IsTwoState" implies that "old" and "fresh" expressions are allowed.
    /// </summary>
    public void ResolveExpression(Expression expr, ResolutionContext resolutionContext) {

#if TEST_TYPE_SYNONYM_TRANSPARENCY
      ResolveExpressionX(expr, resolutionContext);
      // For testing purposes, change the type of "expr" to a type synonym (mwo-ha-ha-ha!)
      var t = expr.Type;
      Contract.Assert(t != null);
      var sd = new TypeSynonymDecl(expr.tok, "type#synonym#transparency#test", new TypeParameter.TypeParameterCharacteristics(false),
        new List<TypeParameter>(), resolutionContext.CodeContext.EnclosingModule, t, null);
      var ts = new UserDefinedType(expr.tok, "type#synonym#transparency#test", sd, new List<Type>(), null);
      expr.DebugTest_ChangeType(ts);
    }
    public void ResolveExpressionX(Expression expr, ResolutionContext resolutionContext) {
#endif
      Contract.Requires(expr != null);
      Contract.Requires(resolutionContext != null);
      Contract.Ensures(expr.Type != null);
      if (expr.Type != null) {
        // expression has already been resolved
        return;
      }

      // The following cases will resolve the subexpressions and will attempt to assign a type of expr.  However, if errors occur
      // and it cannot be determined what the type of expr is, then it is fine to leave expr.Type as null.  In that case, the end
      // of this method will assign proxy type to the expression, which reduces the number of error messages that are produced
      // while type checking the rest of the program.

      if (expr is ParensExpression) {
        var e = (ParensExpression)expr;
        ResolveExpression(e.E, resolutionContext);
        e.ResolvedExpression = e.E;
        e.Type = e.E.Type;

      } else if (expr is ChainingExpression) {
        var e = (ChainingExpression)expr;
        ResolveExpression(e.E, resolutionContext);
        e.ResolvedExpression = e.E;
        e.Type = e.E.Type;

      } else if (expr is NegationExpression) {
        var e = (NegationExpression)expr;
        ResolveExpression(e.E, resolutionContext);
        e.Type = e.E.Type;
        AddXConstraint(e.E.tok, "NumericOrBitvector", e.E.Type, "type of unary - must be of a numeric or bitvector type (instead got {0})");
        // Note, e.ResolvedExpression will be filled in during CheckTypeInference, at which time e.Type has been determined

      } else if (expr is LiteralExpr) {
        LiteralExpr e = (LiteralExpr)expr;

        if (e is StaticReceiverExpr) {
          StaticReceiverExpr eStatic = (StaticReceiverExpr)e;
          ResolveType(eStatic.tok, eStatic.UnresolvedType, resolutionContext, ResolveTypeOptionEnum.InferTypeProxies, null);
          eStatic.Type = eStatic.UnresolvedType;
        } else {
          if (e.Value == null) {
            e.Type = new InferredTypeProxy();
            AddXConstraint(e.tok, "IsNullableRefType", e.Type, "type of 'null' is a reference type, but it is used as {0}");
          } else if (e.Value is BigInteger) {
            var proxy = new InferredTypeProxy();
            e.Type = proxy;
            ConstrainSubtypeRelation(new IntVarietiesSupertype(), e.Type, e.tok, "integer literal used as if it had type {0}", e.Type);
          } else if (e.Value is BaseTypes.BigDec) {
            var proxy = new InferredTypeProxy();
            e.Type = proxy;
            ConstrainSubtypeRelation(new RealVarietiesSupertype(), e.Type, e.tok, "type of real literal is used as {0}", e.Type);
          } else if (e.Value is bool) {
            e.Type = Type.Bool;
          } else if (e is CharLiteralExpr) {
            e.Type = Type.Char;
          } else if (e is StringLiteralExpr) {
            e.Type = Type.String();
            ResolveType(e.tok, e.Type, resolutionContext, ResolveTypeOptionEnum.DontInfer, null);
          } else {
            Contract.Assert(false); throw new cce.UnreachableException();  // unexpected literal type
          }
        }
      } else if (expr is ThisExpr) {
        if (!scope.AllowInstance) {
          reporter.Error(MessageSource.Resolver, expr, "'this' is not allowed in a 'static' context");
        }
        if (currentClass is ClassDecl cd && cd.IsDefaultClass) {
          // there's no type
        } else {
          if (currentClass == null) {
            Contract.Assert(reporter.HasErrors);
          } else {
            expr.Type = GetThisType(expr.tok, currentClass);  // do this regardless of scope.AllowInstance, for better error reporting
          }
        }

      } else if (expr is IdentifierExpr) {
        var e = (IdentifierExpr)expr;
        e.Var = scope.Find(e.Name);
        if (e.Var != null) {
          expr.Type = e.Var.Type;
        } else {
          reporter.Error(MessageSource.Resolver, expr, "Identifier does not denote a local variable, parameter, or bound variable: {0}", e.Name);
        }

      } else if (expr is DatatypeValue) {
        DatatypeValue dtv = (DatatypeValue)expr;
        TopLevelDecl d;
        if (!moduleInfo.TopLevels.TryGetValue(dtv.DatatypeName, out d)) {
          reporter.Error(MessageSource.Resolver, expr.tok, "Undeclared datatype: {0}", dtv.DatatypeName);
        } else if (d is AmbiguousTopLevelDecl) {
          var ad = (AmbiguousTopLevelDecl)d;
          reporter.Error(MessageSource.Resolver, expr.tok, "The name {0} ambiguously refers to a type in one of the modules {1} (try qualifying the type name with the module name)", dtv.DatatypeName, ad.ModuleNames());
        } else if (!(d is DatatypeDecl)) {
          reporter.Error(MessageSource.Resolver, expr.tok, "Expected datatype: {0}", dtv.DatatypeName);
        } else {
          ResolveDatatypeValue(resolutionContext, dtv, (DatatypeDecl)d, null);
        }

      } else if (expr is DisplayExpression) {
        DisplayExpression e = (DisplayExpression)expr;
        Type elementType = new InferredTypeProxy() { KeepConstraints = true };
        foreach (Expression ee in e.Elements) {
          ResolveExpression(ee, resolutionContext);
          Contract.Assert(ee.Type != null);  // follows from postcondition of ResolveExpression
          ConstrainSubtypeRelation(elementType, ee.Type, ee.tok, "All elements of display must have some common supertype (got {0}, but needed type or type of previous elements is {1})", ee.Type, elementType);
        }
        if (expr is SetDisplayExpr) {
          var se = (SetDisplayExpr)expr;
          expr.Type = new SetType(se.Finite, elementType);
        } else if (expr is MultiSetDisplayExpr) {
          expr.Type = new MultiSetType(elementType);
        } else {
          expr.Type = new SeqType(elementType);
        }
      } else if (expr is MapDisplayExpr) {
        MapDisplayExpr e = (MapDisplayExpr)expr;
        Type domainType = new InferredTypeProxy();
        Type rangeType = new InferredTypeProxy();
        foreach (ExpressionPair p in e.Elements) {
          ResolveExpression(p.A, resolutionContext);
          Contract.Assert(p.A.Type != null);  // follows from postcondition of ResolveExpression
          ConstrainSubtypeRelation(domainType, p.A.Type, p.A.tok, "All elements of display must have some common supertype (got {0}, but needed type or type of previous elements is {1})", p.A.Type, domainType);
          ResolveExpression(p.B, resolutionContext);
          Contract.Assert(p.B.Type != null);  // follows from postcondition of ResolveExpression
          ConstrainSubtypeRelation(rangeType, p.B.Type, p.B.tok, "All elements of display must have some common supertype (got {0}, but needed type or type of previous elements is {1})", p.B.Type, rangeType);
        }
        expr.Type = new MapType(e.Finite, domainType, rangeType);
      } else if (expr is NameSegment) {
        var e = (NameSegment)expr;
        ResolveNameSegment(e, true, null, resolutionContext, false);

        if (e.Type is Resolver_IdentifierExpr.ResolverType_Module) {
          reporter.Error(MessageSource.Resolver, e.tok, "name of module ({0}) is used as a variable", e.Name);
          e.ResetTypeAssignment();  // the rest of type checking assumes actual types
        } else if (e.Type is Resolver_IdentifierExpr.ResolverType_Type) {
          reporter.Error(MessageSource.Resolver, e.tok, "name of type ({0}) is used as a variable", e.Name);
          e.ResetTypeAssignment();  // the rest of type checking assumes actual types
        }

      } else if (expr is ExprDotName) {
        var e = (ExprDotName)expr;
        ResolveDotSuffix(e, true, null, resolutionContext, false);
        if (e.Type is Resolver_IdentifierExpr.ResolverType_Module) {
          reporter.Error(MessageSource.Resolver, e.tok, "name of module ({0}) is used as a variable", e.SuffixName);
          e.ResetTypeAssignment();  // the rest of type checking assumes actual types
        } else if (e.Type is Resolver_IdentifierExpr.ResolverType_Type) {
          reporter.Error(MessageSource.Resolver, e.tok, "name of type ({0}) is used as a variable", e.SuffixName);
          e.ResetTypeAssignment();  // the rest of type checking assumes actual types
        }

      } else if (expr is ApplySuffix) {
        var e = (ApplySuffix)expr;
        ResolveApplySuffix(e, resolutionContext, false);

      } else if (expr is MemberSelectExpr) {
        var e = (MemberSelectExpr)expr;
        ResolveExpression(e.Obj, resolutionContext);
        Contract.Assert(e.Obj.Type != null);  // follows from postcondition of ResolveExpression
        NonProxyType tentativeReceiverType;
        var member = ResolveMember(expr.tok, e.Obj.Type, e.MemberName, out tentativeReceiverType);
        if (member == null) {
          // error has already been reported by ResolveMember
        } else if (member is Function) {
          var fn = member as Function;
          e.Member = fn;
          if (fn is TwoStateFunction && !resolutionContext.IsTwoState) {
            reporter.Error(MessageSource.Resolver, e.tok, "a two-state function can be used only in a two-state context");
          }
          // build the type substitution map
          e.TypeApplication_AtEnclosingClass = tentativeReceiverType.TypeArgs;
          e.TypeApplication_JustMember = new List<Type>();
          Dictionary<TypeParameter, Type> subst;
          var ctype = tentativeReceiverType as UserDefinedType;
          if (ctype == null) {
            subst = new Dictionary<TypeParameter, Type>();
          } else {
            subst = TypeParameter.SubstitutionMap(ctype.ResolvedClass.TypeArgs, ctype.TypeArgs);
          }
          foreach (var tp in fn.TypeArgs) {
            Type prox = new InferredTypeProxy();
            subst[tp] = prox;
            e.TypeApplication_JustMember.Add(prox);
          }
          subst = BuildTypeArgumentSubstitute(subst);
          e.Type = SelectAppropriateArrowType(fn.tok,
            fn.Formals.ConvertAll(f => f.Type.Subst(subst)),
            fn.ResultType.Subst(subst),
            fn.Reads.Count != 0, fn.Req.Count != 0);
        } else if (member is Field) {
          var field = (Field)member;
          e.Member = field;
          e.TypeApplication_AtEnclosingClass = tentativeReceiverType.TypeArgs;
          e.TypeApplication_JustMember = new List<Type>();
          if (e.Obj is StaticReceiverExpr && !field.IsStatic) {
            reporter.Error(MessageSource.Resolver, expr, "a field must be selected via an object, not just a class name");
          }
          var ctype = tentativeReceiverType as UserDefinedType;
          if (ctype == null) {
            e.Type = field.Type;
          } else {
            Contract.Assert(ctype.ResolvedClass != null); // follows from postcondition of ResolveMember
            // build the type substitution map
            var subst = TypeParameter.SubstitutionMap(ctype.ResolvedClass.TypeArgs, ctype.TypeArgs);
            e.Type = field.Type.Subst(subst);
          }
        } else {
          reporter.Error(MessageSource.Resolver, expr, "member {0} in type {1} does not refer to a field or a function", e.MemberName, tentativeReceiverType);
        }

      } else if (expr is SeqSelectExpr) {
        SeqSelectExpr e = (SeqSelectExpr)expr;
        ResolveSeqSelectExpr(e, resolutionContext);

      } else if (expr is MultiSelectExpr) {
        MultiSelectExpr e = (MultiSelectExpr)expr;

        ResolveExpression(e.Array, resolutionContext);
        Contract.Assert(e.Array.Type != null);  // follows from postcondition of ResolveExpression
        Contract.Assert(e.Array.Type.TypeArgs != null);  // if it is null, should make a 1-element list with a Proxy
        Type elementType = e.Array.Type.TypeArgs.Count > 0 ?
          e.Array.Type.TypeArgs[0] :
          new InferredTypeProxy();
        ConstrainSubtypeRelation(ResolvedArrayType(e.Array.tok, e.Indices.Count, elementType, resolutionContext, true), e.Array.Type, e.Array,
          "array selection requires an array{0} (got {1})", e.Indices.Count, e.Array.Type);
        int i = 0;
        foreach (Expression idx in e.Indices) {
          Contract.Assert(idx != null);
          ResolveExpression(idx, resolutionContext);
          Contract.Assert(idx.Type != null);  // follows from postcondition of ResolveExpression
          ConstrainToIntegerType(idx, true, "array selection requires integer- or bitvector-based numeric indices (got {0} for index " + i + ")");
          i++;
        }
        e.Type = elementType;

      } else if (expr is SeqUpdateExpr) {
        SeqUpdateExpr e = (SeqUpdateExpr)expr;
        ResolveExpression(e.Seq, resolutionContext);
        Contract.Assert(e.Seq.Type != null);  // follows from postcondition of ResolveExpression
        ResolveExpression(e.Index, resolutionContext);
        ResolveExpression(e.Value, resolutionContext);
        AddXConstraint(expr.tok, "SeqUpdatable", e.Seq.Type, e.Index, e.Value, "update requires a sequence, map, or multiset (got {0})");
        expr.Type = new InferredTypeProxy(); // drop type constraints
        ConstrainSubtypeRelation(
          super: expr.Type, sub: e.Seq.Type, // expr.Type generalizes e.Seq.Type by dropping constraints
          exprForToken: expr,
          msg: "Update expression used with type '{0}'", e.Seq.Type);
      } else if (expr is DatatypeUpdateExpr) {
        var e = (DatatypeUpdateExpr)expr;
        ResolveExpression(e.Root, resolutionContext);
        var ty = PartiallyResolveTypeForMemberSelection(expr.tok, e.Root.Type);
        if (!ty.IsDatatype) {
          reporter.Error(MessageSource.Resolver, expr, "datatype update expression requires a root expression of a datatype (got {0})", ty);
        } else {
          var (ghostLet, compiledLet) = ResolveDatatypeUpdate(expr.tok, e.Root, ty.AsDatatype, e.Updates, resolutionContext,
            out var members, out var legalSourceConstructors);
          Contract.Assert((ghostLet == null) == (compiledLet == null));
          if (ghostLet != null) {
            e.ResolvedExpression = ghostLet; // this might be replaced by e.ResolvedCompiledExpression in CheckIsCompilable
            e.ResolvedCompiledExpression = compiledLet;
            e.Members = members;
            e.LegalSourceConstructors = legalSourceConstructors;
            expr.Type = ghostLet.Type;
          }
        }

      } else if (expr is FunctionCallExpr) {
        var e = (FunctionCallExpr)expr;
        ResolveFunctionCallExpr(e, resolutionContext);

      } else if (expr is ApplyExpr) {
        var e = (ApplyExpr)expr;
        ResolveExpression(e.Function, resolutionContext);
        foreach (var arg in e.Args) {
          ResolveExpression(arg, resolutionContext);
        }

        // TODO: the following should be replaced by a type-class constraint that constrains the types of e.Function, e.Args[*], and e.Type
        var fnType = e.Function.Type.AsArrowType;
        if (fnType == null) {
          reporter.Error(MessageSource.Resolver, e.tok,
            "non-function expression (of type {0}) is called with parameters", e.Function.Type);
        } else if (fnType.Arity != e.Args.Count) {
          reporter.Error(MessageSource.Resolver, e.tok,
            "wrong number of arguments to function application (function type '{0}' expects {1}, got {2})", fnType,
            fnType.Arity, e.Args.Count);
        } else {
          for (var i = 0; i < fnType.Arity; i++) {
            AddAssignableConstraint(e.Args[i].tok, fnType.Args[i], e.Args[i].Type,
              "type mismatch for argument" + (fnType.Arity == 1 ? "" : " " + i) + " (function expects {0}, got {1})");
          }
        }

        expr.Type = fnType == null ? new InferredTypeProxy() : fnType.Result;

      } else if (expr is SeqConstructionExpr) {
        var e = (SeqConstructionExpr)expr;
        var elementType = e.ExplicitElementType ?? new InferredTypeProxy();
        ResolveType(e.tok, elementType, resolutionContext, ResolveTypeOptionEnum.InferTypeProxies, null);
        ResolveExpression(e.N, resolutionContext);
        ConstrainToIntegerType(e.N, false, "sequence construction must use an integer-based expression for the sequence size (got {0})");
        ResolveExpression(e.Initializer, resolutionContext);
        var arrowType = new ArrowType(e.tok, builtIns.ArrowTypeDecls[1], new List<Type>() { builtIns.Nat() }, elementType);
        var hintString = " (perhaps write '_ =>' in front of the expression you gave in order to make it an arrow type)";
        ConstrainSubtypeRelation(arrowType, e.Initializer.Type, e.Initializer, "sequence-construction initializer expression expected to have type '{0}' (instead got '{1}'){2}",
          arrowType, e.Initializer.Type, new LazyString_OnTypeEquals(elementType, e.Initializer.Type, hintString));
        expr.Type = new SeqType(elementType);

      } else if (expr is MultiSetFormingExpr) {
        MultiSetFormingExpr e = (MultiSetFormingExpr)expr;
        ResolveExpression(e.E, resolutionContext);
        var elementType = new InferredTypeProxy();
        AddXConstraint(e.E.tok, "MultiSetConvertible", e.E.Type, elementType, "can only form a multiset from a seq or set (got {0})");
        expr.Type = new MultiSetType(elementType);

      } else if (expr is OldExpr) {
        var e = (OldExpr)expr;
        e.AtLabel = ResolveDominatingLabelInExpr(expr.tok, e.At, "old", resolutionContext);
        ResolveExpression(e.E, new ResolutionContext(resolutionContext.CodeContext, false) with { InOld = true });
        expr.Type = e.E.Type;

      } else if (expr is UnchangedExpr) {
        var e = (UnchangedExpr)expr;
        e.AtLabel = ResolveDominatingLabelInExpr(expr.tok, e.At, "unchanged", resolutionContext);
        foreach (var fe in e.Frame) {
          ResolveFrameExpression(fe, FrameExpressionUse.Unchanged, resolutionContext);
        }
        expr.Type = Type.Bool;

      } else if (expr is FreshExpr) {
        var e = (FreshExpr)expr;
        ResolveExpression(e.E, resolutionContext);
        e.AtLabel = ResolveDominatingLabelInExpr(expr.tok, e.At, "fresh", resolutionContext);
        // the type of e.E must be either an object or a set/seq of objects
        AddXConstraint(expr.tok, "Freshable", e.E.Type, "the argument of a fresh expression must denote an object or a set or sequence of objects (instead got {0})");
        expr.Type = Type.Bool;

      } else if (expr is UnaryOpExpr) {
        var e = (UnaryOpExpr)expr;
        ResolveExpression(e.E, resolutionContext);
        Contract.Assert(e.E.Type != null);  // follows from postcondition of ResolveExpression
        switch (e.Op) {
          case UnaryOpExpr.Opcode.Not:
            AddXConstraint(e.E.tok, "BooleanBits", e.E.Type, "logical/bitwise negation expects a boolean or bitvector argument (instead got {0})");
            expr.Type = e.E.Type;
            break;
          case UnaryOpExpr.Opcode.Cardinality:
            AddXConstraint(expr.tok, "Sizeable", e.E.Type, "size operator expects a collection argument (instead got {0})");
            expr.Type = Type.Int;
            break;
          case UnaryOpExpr.Opcode.Allocated:
            // the argument is allowed to have any type at all
            expr.Type = Type.Bool;
            if (2 <= DafnyOptions.O.Allocated &&
              ((resolutionContext.CodeContext is Function && !resolutionContext.InOld) || resolutionContext.CodeContext is ConstantField || CodeContextWrapper.Unwrap(resolutionContext.CodeContext) is RedirectingTypeDecl)) {
              var declKind = CodeContextWrapper.Unwrap(resolutionContext.CodeContext) is RedirectingTypeDecl redir ? redir.WhatKind : ((MemberDecl)resolutionContext.CodeContext).WhatKind;
              reporter.Error(MessageSource.Resolver, expr, "a {0} definition is not allowed to depend on the set of allocated references", declKind);
            }
            break;
          default:
            Contract.Assert(false); throw new cce.UnreachableException();  // unexpected unary operator
        }

        // We do not have enough information to compute `e.ResolvedOp` yet.
        // For binary operators the computation happens in `CheckTypeInference`.
        // For unary operators it happens lazily in the getter of `e.ResolvedOp`.
      } else if (expr is ConversionExpr) {
        var e = (ConversionExpr)expr;
        ResolveExpression(e.E, resolutionContext);
        var prevErrorCount = reporter.Count(ErrorLevel.Error);
        ResolveType(e.tok, e.ToType, resolutionContext, new ResolveTypeOption(ResolveTypeOptionEnum.InferTypeProxies), null);
        if (reporter.Count(ErrorLevel.Error) == prevErrorCount) {
          if (e.ToType.IsNumericBased(Type.NumericPersuasion.Int)) {
            AddXConstraint(expr.tok, "NumericOrBitvectorOrCharOrORDINAL", e.E.Type, "type conversion to an int-based type is allowed only from numeric and bitvector types, char, and ORDINAL (got {0})");
          } else if (e.ToType.IsNumericBased(Type.NumericPersuasion.Real)) {
            AddXConstraint(expr.tok, "NumericOrBitvectorOrCharOrORDINAL", e.E.Type, "type conversion to a real-based type is allowed only from numeric and bitvector types, char, and ORDINAL (got {0})");
          } else if (e.ToType.IsBitVectorType) {
            AddXConstraint(expr.tok, "NumericOrBitvectorOrCharOrORDINAL", e.E.Type, "type conversion to a bitvector-based type is allowed only from numeric and bitvector types, char, and ORDINAL (got {0})");
          } else if (e.ToType.IsCharType) {
            AddXConstraint(expr.tok, "NumericOrBitvectorOrCharOrORDINAL", e.E.Type, "type conversion to a char type is allowed only from numeric and bitvector types, char, and ORDINAL (got {0})");
          } else if (e.ToType.IsBigOrdinalType) {
            AddXConstraint(expr.tok, "NumericOrBitvectorOrCharOrORDINAL", e.E.Type, "type conversion to an ORDINAL type is allowed only from numeric and bitvector types, char, and ORDINAL (got {0})");
          } else if (e.ToType.IsRefType) {
            AddAssignableConstraint(expr.tok, e.ToType, e.E.Type, "type cast to reference type '{0}' must be from an expression assignable to it (got '{1}')");
          } else {
            reporter.Error(MessageSource.Resolver, expr, "type conversions are not supported to this type (got {0})", e.ToType);
          }
          e.Type = e.ToType;
        } else {
          e.Type = new InferredTypeProxy();
        }

      } else if (expr is TypeTestExpr) {
        var e = (TypeTestExpr)expr;
        ResolveExpression(e.E, resolutionContext);
        var prevErrorCount = reporter.Count(ErrorLevel.Error);
        ResolveType(e.tok, e.ToType, resolutionContext, new ResolveTypeOption(ResolveTypeOptionEnum.InferTypeProxies), null);
        AddAssignableConstraint(expr.tok, e.ToType, e.E.Type, "type test for type '{0}' must be from an expression assignable to it (got '{1}')");
        e.Type = Type.Bool;

      } else if (expr is BinaryExpr) {

        BinaryExpr e = (BinaryExpr)expr;
        ResolveExpression(e.E0, resolutionContext);
        Contract.Assert(e.E0.Type != null);  // follows from postcondition of ResolveExpression
        ResolveExpression(e.E1, resolutionContext);
        Contract.Assert(e.E1.Type != null);  // follows from postcondition of ResolveExpression

        switch (e.Op) {
          case BinaryExpr.Opcode.Iff:
          case BinaryExpr.Opcode.Imp:
          case BinaryExpr.Opcode.Exp:
          case BinaryExpr.Opcode.And:
          case BinaryExpr.Opcode.Or: {
              ConstrainSubtypeRelation(Type.Bool, e.E0.Type, expr, "first argument to {0} must be of type bool (instead got {1})", BinaryExpr.OpcodeString(e.Op), e.E0.Type);
              var secondArgumentDescription = e.E1.tok is QuantifiedVariableRangeToken
                ? "range of quantified variable" : "second argument to {0}";
              ConstrainSubtypeRelation(Type.Bool, e.E1.Type, expr, secondArgumentDescription + " must be of type bool (instead got {1})", BinaryExpr.OpcodeString(e.Op), e.E1.Type);
              expr.Type = Type.Bool;
              break;
            }

          case BinaryExpr.Opcode.Eq:
          case BinaryExpr.Opcode.Neq:
            AddXConstraint(expr.tok, "Equatable", e.E0.Type, e.E1.Type, "arguments must have comparable types (got {0} and {1})");
            expr.Type = Type.Bool;
            break;

          case BinaryExpr.Opcode.Disjoint:
            Type disjointArgumentsType = new InferredTypeProxy();
            ConstrainSubtypeRelation(disjointArgumentsType, e.E0.Type, expr, "arguments to {2} must have a common supertype (got {0} and {1})", e.E0.Type, e.E1.Type, BinaryExpr.OpcodeString(e.Op));
            ConstrainSubtypeRelation(disjointArgumentsType, e.E1.Type, expr, "arguments to {2} must have a common supertype (got {0} and {1})", e.E0.Type, e.E1.Type, BinaryExpr.OpcodeString(e.Op));
            AddXConstraint(expr.tok, "Disjointable", disjointArgumentsType, "arguments must be of a set or multiset type (got {0})");
            expr.Type = Type.Bool;
            break;

          case BinaryExpr.Opcode.Lt:
          case BinaryExpr.Opcode.Le: {
              if (e.Op == BinaryExpr.Opcode.Lt && (PartiallyResolveTypeForMemberSelection(e.E0.tok, e.E0.Type).IsIndDatatype || e.E0.Type.IsTypeParameter || PartiallyResolveTypeForMemberSelection(e.E1.tok, e.E1.Type).IsIndDatatype)) {
                AddXConstraint(expr.tok, "RankOrderable", e.E0.Type, e.E1.Type, "arguments to rank comparison must be datatypes (got {0} and {1})");
                e.ResolvedOp = BinaryExpr.ResolvedOpcode.RankLt;
              } else {
                var cmpType = new InferredTypeProxy();
                var err = new TypeConstraint.ErrorMsgWithToken(expr.tok, "arguments to {2} must have a common supertype (got {0} and {1})", e.E0.Type, e.E1.Type, BinaryExpr.OpcodeString(e.Op));
                ConstrainSubtypeRelation(cmpType, e.E0.Type, err);
                ConstrainSubtypeRelation(cmpType, e.E1.Type, err);
                AddXConstraint(expr.tok, "Orderable_Lt", e.E0.Type, e.E1.Type,
                  "arguments to " + BinaryExpr.OpcodeString(e.Op) + " must be of a numeric type, bitvector type, ORDINAL, char, a sequence type, or a set-like type (instead got {0} and {1})");
              }
              expr.Type = Type.Bool;
            }
            break;

          case BinaryExpr.Opcode.Gt:
          case BinaryExpr.Opcode.Ge: {
              if (e.Op == BinaryExpr.Opcode.Gt && (PartiallyResolveTypeForMemberSelection(e.E0.tok, e.E0.Type).IsIndDatatype || PartiallyResolveTypeForMemberSelection(e.E1.tok, e.E1.Type).IsIndDatatype || e.E1.Type.IsTypeParameter)) {
                AddXConstraint(expr.tok, "RankOrderable", e.E1.Type, e.E0.Type, "arguments to rank comparison must be datatypes (got {1} and {0})");
                e.ResolvedOp = BinaryExpr.ResolvedOpcode.RankGt;
              } else {
                var cmpType = new InferredTypeProxy();
                var err = new TypeConstraint.ErrorMsgWithToken(expr.tok, "arguments to {2} must have a common supertype (got {0} and {1})", e.E0.Type, e.E1.Type, BinaryExpr.OpcodeString(e.Op));
                ConstrainSubtypeRelation(cmpType, e.E0.Type, err);
                ConstrainSubtypeRelation(cmpType, e.E1.Type, err);
                AddXConstraint(expr.tok, "Orderable_Gt", e.E0.Type, e.E1.Type,
                  "arguments to " + BinaryExpr.OpcodeString(e.Op) + " must be of a numeric type, bitvector type, ORDINAL, char, or a set-like type (instead got {0} and {1})");
              }
              expr.Type = Type.Bool;
            }
            break;

          case BinaryExpr.Opcode.LeftShift:
          case BinaryExpr.Opcode.RightShift: {
              expr.Type = new InferredTypeProxy();
              AddXConstraint(e.tok, "IsBitvector", expr.Type, "type of " + BinaryExpr.OpcodeString(e.Op) + " must be a bitvector type (instead got {0})");
              ConstrainSubtypeRelation(expr.Type, e.E0.Type, expr.tok, "type of left argument to " + BinaryExpr.OpcodeString(e.Op) + " ({0}) must agree with the result type ({1})", e.E0.Type, expr.Type);
              AddXConstraint(expr.tok, "IntLikeOrBitvector", e.E1.Type, "type of right argument to " + BinaryExpr.OpcodeString(e.Op) + " ({0}) must be an integer-numeric or bitvector type");
            }
            break;

          case BinaryExpr.Opcode.Add: {
              expr.Type = new InferredTypeProxy();
              AddXConstraint(e.tok, "Plussable", expr.Type, "type of + must be of a numeric type, a bitvector type, ORDINAL, char, a sequence type, or a set-like or map-like type (instead got {0})");
              ConstrainSubtypeRelation(expr.Type, e.E0.Type, expr.tok, "type of left argument to + ({0}) must agree with the result type ({1})", e.E0.Type, expr.Type);
              ConstrainSubtypeRelation(expr.Type, e.E1.Type, expr.tok, "type of right argument to + ({0}) must agree with the result type ({1})", e.E1.Type, expr.Type);
            }
            break;

          case BinaryExpr.Opcode.Sub: {
              expr.Type = new InferredTypeProxy();
              AddXConstraint(e.tok, "Minusable", expr.Type, "type of - must be of a numeric type, bitvector type, ORDINAL, char, or a set-like or map-like type (instead got {0})");
              ConstrainSubtypeRelation(expr.Type, e.E0.Type, expr.tok, "type of left argument to - ({0}) must agree with the result type ({1})", e.E0.Type, expr.Type);
              // The following handles map subtraction, but does not in an unfortunately restrictive way.
              // First, it would be nice to delay the decision of it this is a map subtraction or not. This settles
              // for the simple way to decide based on what is currently known about the result type, which is also
              // done, for example, when deciding if "<" denotes rank ordering on datatypes.
              // Second, for map subtraction, it would be nice to allow the right-hand operand to be either a set or
              // an iset. That would also lead to further complexity in the code, so this code restricts the right-hand
              // operand to be a set.
              var eType = PartiallyResolveTypeForMemberSelection(expr.tok, expr.Type).AsMapType;
              if (eType != null) {
                // allow "map - set == map"
                var expected = new SetType(true, eType.Domain);
                ConstrainSubtypeRelation(expected, e.E1.Type, expr.tok, "map subtraction expects right-hand operand to have type {0} (instead got {1})", expected, e.E1.Type);
              } else {
                ConstrainSubtypeRelation(expr.Type, e.E1.Type, expr.tok, "type of right argument to - ({0}) must agree with the result type ({1})", e.E1.Type, expr.Type);
              }
            }
            break;

          case BinaryExpr.Opcode.Mul: {
              expr.Type = new InferredTypeProxy();
              AddXConstraint(e.tok, "Mullable", expr.Type, "type of * must be of a numeric type, bitvector type, or a set-like type (instead got {0})");
              ConstrainSubtypeRelation(expr.Type, e.E0.Type, expr.tok, "type of left argument to * ({0}) must agree with the result type ({1})", e.E0.Type, expr.Type);
              ConstrainSubtypeRelation(expr.Type, e.E1.Type, expr.tok, "type of right argument to * ({0}) must agree with the result type ({1})", e.E1.Type, expr.Type);
            }
            break;

          case BinaryExpr.Opcode.In:
          case BinaryExpr.Opcode.NotIn:
            var subjectDescription = e.E1.tok is QuantifiedVariableDomainToken
              ? "domain of quantified variable" : "second argument to \"" + BinaryExpr.OpcodeString(e.Op) + "\"";
            AddXConstraint(expr.tok, "Innable", e.E1.Type, e.E0.Type, subjectDescription + " must be a set, multiset, or sequence with elements of type {1}, or a map with domain {1} (instead got {0})");
            expr.Type = Type.Bool;
            break;

          case BinaryExpr.Opcode.Div:
            expr.Type = new InferredTypeProxy();
            AddXConstraint(expr.tok, "NumericOrBitvector", expr.Type, "arguments to " + BinaryExpr.OpcodeString(e.Op) + " must be numeric or bitvector types (got {0})");
            ConstrainSubtypeRelation(expr.Type, e.E0.Type,
              expr, "type of left argument to " + BinaryExpr.OpcodeString(e.Op) + " ({0}) must agree with the result type ({1})",
              e.E0.Type, expr.Type);
            ConstrainSubtypeRelation(expr.Type, e.E1.Type,
              expr, "type of right argument to " + BinaryExpr.OpcodeString(e.Op) + " ({0}) must agree with the result type ({1})",
              e.E1.Type, expr.Type);
            break;

          case BinaryExpr.Opcode.Mod:
            expr.Type = new InferredTypeProxy();
            AddXConstraint(expr.tok, "IntLikeOrBitvector", expr.Type, "arguments to " + BinaryExpr.OpcodeString(e.Op) + " must be integer-numeric or bitvector types (got {0})");
            ConstrainSubtypeRelation(expr.Type, e.E0.Type,
              expr, "type of left argument to " + BinaryExpr.OpcodeString(e.Op) + " ({0}) must agree with the result type ({1})",
              e.E0.Type, expr.Type);
            ConstrainSubtypeRelation(expr.Type, e.E1.Type,
              expr, "type of right argument to " + BinaryExpr.OpcodeString(e.Op) + " ({0}) must agree with the result type ({1})",
              e.E1.Type, expr.Type);
            break;

          case BinaryExpr.Opcode.BitwiseAnd:
          case BinaryExpr.Opcode.BitwiseOr:
          case BinaryExpr.Opcode.BitwiseXor:
            expr.Type = NewIntegerBasedProxy(expr.tok);
            var errFormat = "first argument to " + BinaryExpr.OpcodeString(e.Op) + " must be of a bitvector type (instead got {0})";
            ConstrainSubtypeRelation(expr.Type, e.E0.Type, expr, errFormat, e.E0.Type);
            AddXConstraint(expr.tok, "IsBitvector", e.E0.Type, errFormat);
            errFormat = "second argument to " + BinaryExpr.OpcodeString(e.Op) + " must be of a bitvector type (instead got {0})";
            ConstrainSubtypeRelation(expr.Type, e.E1.Type, expr, errFormat, e.E1.Type);
            AddXConstraint(expr.tok, "IsBitvector", e.E1.Type, errFormat);
            break;

          default:
            Contract.Assert(false); throw new cce.UnreachableException();  // unexpected operator
        }
        // We should also fill in e.ResolvedOp, but we may not have enough information for that yet.  So, instead, delay
        // setting e.ResolvedOp until inside CheckTypeInference.

      } else if (expr is TernaryExpr) {
        var e = (TernaryExpr)expr;
        ResolveExpression(e.E0, resolutionContext);
        ResolveExpression(e.E1, resolutionContext);
        ResolveExpression(e.E2, resolutionContext);
        switch (e.Op) {
          case TernaryExpr.Opcode.PrefixEqOp:
          case TernaryExpr.Opcode.PrefixNeqOp:
            AddXConstraint(expr.tok, "IntOrORDINAL", e.E0.Type, "prefix-equality limit argument must be an ORDINAL or integer expression (got {0})");
            AddXConstraint(expr.tok, "Equatable", e.E1.Type, e.E2.Type, "arguments must have the same type (got {0} and {1})");
            AddXConstraint(expr.tok, "IsCoDatatype", e.E1.Type, "arguments to prefix equality must be codatatypes (instead of {0})");
            expr.Type = Type.Bool;
            break;
          default:
            Contract.Assert(false);  // unexpected ternary operator
            break;
        }

      } else if (expr is LetExpr) {
        var e = (LetExpr)expr;
        if (e.Exact) {
          foreach (var rhs in e.RHSs) {
            ResolveExpression(rhs, resolutionContext);
          }
          scope.PushMarker();
          if (e.LHSs.Count != e.RHSs.Count) {
            reporter.Error(MessageSource.Resolver, expr, "let expression must have same number of LHSs (found {0}) as RHSs (found {1})", e.LHSs.Count, e.RHSs.Count);
          }
          var i = 0;
          foreach (var lhs in e.LHSs) {
            var rhsType = i < e.RHSs.Count ? e.RHSs[i].Type : new InferredTypeProxy();
            ResolveCasePattern(lhs, rhsType, resolutionContext);
            // Check for duplicate names now, because not until after resolving the case pattern do we know if identifiers inside it refer to bound variables or nullary constructors
            var c = 0;
            foreach (var v in lhs.Vars) {
              ScopePushAndReport(scope, v, "let-variable");
              c++;
            }
            if (c == 0) {
              // Every identifier-looking thing in the pattern resolved to a constructor; that is, this LHS is a constant literal
              reporter.Error(MessageSource.Resolver, lhs.tok, "LHS is a constant literal; to be legal, it must introduce at least one bound variable");
            }
            i++;
          }
        } else {
          // let-such-that expression
          if (e.RHSs.Count != 1) {
            reporter.Error(MessageSource.Resolver, expr, "let-such-that expression must have just one RHS (found {0})", e.RHSs.Count);
          }
          // the bound variables are in scope in the RHS of a let-such-that expression
          scope.PushMarker();
          foreach (var lhs in e.LHSs) {
            Contract.Assert(lhs.Var != null);  // the parser already checked that every LHS is a BoundVar, not a general pattern
            var v = lhs.Var;
            ScopePushAndReport(scope, v, "let-variable");
            ResolveType(v.tok, v.Type, resolutionContext, ResolveTypeOptionEnum.InferTypeProxies, null);
          }
          foreach (var rhs in e.RHSs) {
            ResolveExpression(rhs, resolutionContext);
            ConstrainTypeExprBool(rhs, "type of RHS of let-such-that expression must be boolean (got {0})");
          }
        }
        ResolveExpression(e.Body, resolutionContext);
        ResolveAttributes(e, resolutionContext);
        scope.PopMarker();
        expr.Type = e.Body.Type;
      } else if (expr is LetOrFailExpr) {
        var e = (LetOrFailExpr)expr;
        ResolveLetOrFailExpr(e, resolutionContext);
      } else if (expr is QuantifierExpr) {
        var e = (QuantifierExpr)expr;
        Contract.Assert(e.SplitQuantifier == null); // No split quantifiers during resolution
        int prevErrorCount = reporter.Count(ErrorLevel.Error);
        scope.PushMarker();
        foreach (BoundVar v in e.BoundVars) {
          ScopePushAndReport(scope, v, "bound-variable");
          var option = new ResolveTypeOption(ResolveTypeOptionEnum.InferTypeProxies);
          ResolveType(v.tok, v.Type, resolutionContext, option, null);
        }
        if (e.Range != null) {
          ResolveExpression(e.Range, resolutionContext);
          Contract.Assert(e.Range.Type != null);  // follows from postcondition of ResolveExpression
          ConstrainTypeExprBool(e.Range, "range of quantifier must be of type bool (instead got {0})");
        }
        ResolveExpression(e.Term, resolutionContext);
        Contract.Assert(e.Term.Type != null);  // follows from postcondition of ResolveExpression
        ConstrainTypeExprBool(e.Term, "body of quantifier must be of type bool (instead got {0})");
        // Since the body is more likely to infer the types of the bound variables, resolve it
        // first (above) and only then resolve the attributes (below).
        ResolveAttributes(e, resolutionContext);
        scope.PopMarker();
        expr.Type = Type.Bool;

      } else if (expr is SetComprehension) {
        var e = (SetComprehension)expr;
        int prevErrorCount = reporter.Count(ErrorLevel.Error);
        scope.PushMarker();
        foreach (BoundVar v in e.BoundVars) {
          ScopePushAndReport(scope, v, "bound-variable");
          ResolveType(v.tok, v.Type, resolutionContext, ResolveTypeOptionEnum.InferTypeProxies, null);
          var inferredProxy = v.Type as InferredTypeProxy;
          if (inferredProxy != null) {
            Contract.Assert(!inferredProxy.KeepConstraints);  // in general, this proxy is inferred to be a base type
          }
        }
        ResolveExpression(e.Range, resolutionContext);
        Contract.Assert(e.Range.Type != null);  // follows from postcondition of ResolveExpression
        ConstrainTypeExprBool(e.Range, "range of comprehension must be of type bool (instead got {0})");
        ResolveExpression(e.Term, resolutionContext);
        Contract.Assert(e.Term.Type != null);  // follows from postcondition of ResolveExpression

        ResolveAttributes(e, resolutionContext);
        scope.PopMarker();
        expr.Type = new SetType(e.Finite, e.Term.Type);

      } else if (expr is MapComprehension) {
        var e = (MapComprehension)expr;
        int prevErrorCount = reporter.Count(ErrorLevel.Error);
        scope.PushMarker();
        Contract.Assert(e.BoundVars.Count == 1 || (1 < e.BoundVars.Count && e.TermLeft != null));
        foreach (BoundVar v in e.BoundVars) {
          ScopePushAndReport(scope, v, "bound-variable");
          ResolveType(v.tok, v.Type, resolutionContext, ResolveTypeOptionEnum.InferTypeProxies, null);
          var inferredProxy = v.Type as InferredTypeProxy;
          if (inferredProxy != null) {
            Contract.Assert(!inferredProxy.KeepConstraints);  // in general, this proxy is inferred to be a base type
          }
        }
        ResolveExpression(e.Range, resolutionContext);
        Contract.Assert(e.Range.Type != null);  // follows from postcondition of ResolveExpression
        ConstrainTypeExprBool(e.Range, "range of comprehension must be of type bool (instead got {0})");
        if (e.TermLeft != null) {
          ResolveExpression(e.TermLeft, resolutionContext);
          Contract.Assert(e.TermLeft.Type != null);  // follows from postcondition of ResolveExpression
        }
        ResolveExpression(e.Term, resolutionContext);
        Contract.Assert(e.Term.Type != null);  // follows from postcondition of ResolveExpression

        ResolveAttributes(e, resolutionContext);
        scope.PopMarker();
        expr.Type = new MapType(e.Finite, e.TermLeft != null ? e.TermLeft.Type : e.BoundVars[0].Type, e.Term.Type);

      } else if (expr is LambdaExpr) {
        var e = (LambdaExpr)expr;
        int prevErrorCount = reporter.Count(ErrorLevel.Error);
        scope.PushMarker();
        foreach (BoundVar v in e.BoundVars) {
          ScopePushAndReport(scope, v, "bound-variable");
          ResolveType(v.tok, v.Type, resolutionContext, ResolveTypeOptionEnum.InferTypeProxies, null);
        }

        if (e.Range != null) {
          ResolveExpression(e.Range, resolutionContext);
          Contract.Assert(e.Range.Type != null);  // follows from postcondition of ResolveExpression
          ConstrainTypeExprBool(e.Range, "Precondition must be boolean (got {0})");
        }
        foreach (var read in e.Reads) {
          ResolveFrameExpression(read, FrameExpressionUse.Reads, resolutionContext);
        }
        ResolveExpression(e.Term, resolutionContext);
        Contract.Assert(e.Term.Type != null);
        scope.PopMarker();
        expr.Type = SelectAppropriateArrowType(e.tok, e.BoundVars.ConvertAll(v => v.Type), e.Body.Type, e.Reads.Count != 0, e.Range != null);
      } else if (expr is WildcardExpr) {
        expr.Type = new SetType(true, builtIns.ObjectQ());
      } else if (expr is StmtExpr) {
        var e = (StmtExpr)expr;
        int prevErrorCount = reporter.Count(ErrorLevel.Error);

        ResolveStatement(e.S, resolutionContext);
        if (reporter.Count(ErrorLevel.Error) == prevErrorCount) {
          var r = e.S as UpdateStmt;
          if (r != null && r.ResolvedStatements.Count == 1) {
            var call = r.ResolvedStatements[0] as CallStmt;
            if (call.Method is TwoStateLemma && !resolutionContext.IsTwoState) {
              reporter.Error(MessageSource.Resolver, call, "two-state lemmas can only be used in two-state contexts");
            }
          }
        }

        ResolveExpression(e.E, resolutionContext);
        Contract.Assert(e.E.Type != null);  // follows from postcondition of ResolveExpression
        expr.Type = e.E.Type;

      } else if (expr is ITEExpr) {
        ITEExpr e = (ITEExpr)expr;
        ResolveExpression(e.Test, resolutionContext);
        Contract.Assert(e.Test.Type != null);  // follows from postcondition of ResolveExpression
        ResolveExpression(e.Thn, resolutionContext);
        Contract.Assert(e.Thn.Type != null);  // follows from postcondition of ResolveExpression
        ResolveExpression(e.Els, resolutionContext);
        Contract.Assert(e.Els.Type != null);  // follows from postcondition of ResolveExpression
        ConstrainTypeExprBool(e.Test, "guard condition in if-then-else expression must be a boolean (instead got {0})");
        expr.Type = new InferredTypeProxy();
        ConstrainSubtypeRelation(expr.Type, e.Thn.Type, expr, "the two branches of an if-then-else expression must have the same type (got {0} and {1})", e.Thn.Type, e.Els.Type);
        ConstrainSubtypeRelation(expr.Type, e.Els.Type, expr, "the two branches of an if-then-else expression must have the same type (got {0} and {1})", e.Thn.Type, e.Els.Type);

      } else if (expr is NestedMatchExpr nestedMatchExpr) {
        ResolveNestedMatchExpr(nestedMatchExpr, resolutionContext);
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected expression
      }

      if (expr.Type == null) {
        // some resolution error occurred
        expr.Type = new InferredTypeProxy();
      }
    }

    void ResolveTypeParameters(List<TypeParameter/*!*/>/*!*/ tparams, bool emitErrors, TypeParameter.ParentType/*!*/ parent) {
      Contract.Requires(tparams != null);
      Contract.Requires(parent != null);
      // push non-duplicated type parameter names
      int index = 0;
      foreach (TypeParameter tp in tparams) {
        if (emitErrors) {
          // we're seeing this TypeParameter for the first time
          tp.Parent = parent;
          tp.PositionalIndex = index;
        }
        var r = allTypeParameters.Push(tp.Name, tp);
        if (emitErrors) {
          if (r == Scope<TypeParameter>.PushResult.Duplicate) {
            reporter.Error(MessageSource.Resolver, ErrorID.None, tp, "Duplicate type-parameter name: {0}", tp.Name);
          } else if (r == Scope<TypeParameter>.PushResult.Shadow) {
            reporter.Warning(MessageSource.Resolver, ErrorID.None, tp.tok, "Shadowed type-parameter name: {0}", tp.Name);
          }
        }
      }
    }

    private bool ConstrainSubtypeRelation(Type super, Type sub, Expression exprForToken, string msg, params object[] msgArgs) {
      Contract.Requires(sub != null);
      Contract.Requires(super != null);
      Contract.Requires(exprForToken != null);
      Contract.Requires(msg != null);
      Contract.Requires(msgArgs != null);
      return ConstrainSubtypeRelation(super, sub, exprForToken.tok, msg, msgArgs);
    }

    public void ConstrainTypeExprBool(Expression e, string msg) {
      Contract.Requires(e != null);
      Contract.Requires(msg != null);  // expected to have a {0} part
      ConstrainSubtypeRelation(Type.Bool, e.Type, e, msg, e.Type);
    }

    public bool ConstrainSubtypeRelation(Type super, Type sub, IToken tok, string msg, params object[] msgArgs) {
      Contract.Requires(sub != null);
      Contract.Requires(super != null);
      Contract.Requires(tok != null);
      Contract.Requires(msg != null);
      Contract.Requires(msgArgs != null);
      return ConstrainSubtypeRelation(super, sub, new TypeConstraint.ErrorMsgWithToken(tok, msg, msgArgs));
    }

    private void ConstrainAssignable(NonProxyType lhs, Type rhs, TypeConstraint.ErrorMsg errMsg, out bool moreXConstraints, bool allowDecisions) {
      Contract.Requires(lhs != null);
      Contract.Requires(rhs != null);
      Contract.Requires(errMsg != null);

      DetermineRootLeaf(lhs, out var isRoot, out _, out _, out _);
      if (isRoot) {
        ConstrainSubtypeRelation(lhs, rhs, errMsg, true, allowDecisions);
        moreXConstraints = false;
      } else {
        var lhsWithProxyArgs = Type.HeadWithProxyArgs(lhs);
        ConstrainSubtypeRelation(lhsWithProxyArgs, rhs, errMsg, false, allowDecisions);
        ConstrainAssignableTypeArgs(lhs, lhsWithProxyArgs.TypeArgs, lhs.TypeArgs, errMsg, out moreXConstraints);
        if (lhs.AsCollectionType == null) {
          var sameHead = Type.SameHead(lhs, rhs);
          if (!sameHead && lhs is UserDefinedType udtLhs && rhs is UserDefinedType udtRhs) {
            // also allow the case where lhs is a possibly-null type and rhs is a non-null type
            sameHead = udtLhs.ResolvedClass == (udtRhs.ResolvedClass as NonNullTypeDecl)?.Class;
          }
          if (sameHead) {
            bool more2;
            ConstrainAssignableTypeArgs(lhs, lhs.TypeArgs, rhs.TypeArgs, errMsg, out more2);
            moreXConstraints = moreXConstraints || more2;
          }
        }
      }
    }

    private void ConstrainAssignableTypeArgs(Type typeHead, List<Type> A, List<Type> B, TypeConstraint.ErrorMsg errMsg, out bool moreXConstraints) {
      Contract.Requires(typeHead != null);
      Contract.Requires(A != null);
      Contract.Requires(B != null);
      Contract.Requires(A.Count == B.Count);
      Contract.Requires(errMsg != null);

      var tok = errMsg.Tok;
      if (B.Count == 0) {
        // all done
        moreXConstraints = false;
      } else if (typeHead is MapType) {
        var em = new TypeConstraint.ErrorMsgWithBase(errMsg, "covariance for type parameter at index 0 expects {1} <: {0}", A[0], B[0]);
        AddAssignableConstraint(tok, A[0], B[0], em);
        em = new TypeConstraint.ErrorMsgWithBase(errMsg, "covariance for type parameter at index 1 expects {1} <: {0}", A[1], B[1]);
        AddAssignableConstraint(tok, A[1], B[1], em);
        moreXConstraints = true;
      } else if (typeHead is CollectionType) {
        var em = new TypeConstraint.ErrorMsgWithBase(errMsg, "covariance for type parameter expects {1} <: {0}", A[0], B[0]);
        AddAssignableConstraint(tok, A[0], B[0], em);
        moreXConstraints = true;
      } else {
        var udt = (UserDefinedType)typeHead;  // note, collections, maps, and user-defined types are the only one with TypeArgs.Count != 0
        var cl = udt.ResolvedClass;
        Contract.Assert(cl != null);
        Contract.Assert(cl.TypeArgs.Count == B.Count);
        moreXConstraints = false;
        for (int i = 0; i < B.Count; i++) {
          var msgFormat = "variance for type parameter" + (B.Count == 1 ? "" : " at index " + i) + " expects {0} {1} {2}";
          if (cl.TypeArgs[i].Variance == TypeParameter.TPVariance.Co) {
            var em = new TypeConstraint.ErrorMsgWithBase(errMsg, "co" + msgFormat, A[i], ":>", B[i]);
            AddAssignableConstraint(tok, A[i], B[i], em);
            moreXConstraints = true;
          } else if (cl.TypeArgs[i].Variance == TypeParameter.TPVariance.Contra) {
            var em = new TypeConstraint.ErrorMsgWithBase(errMsg, "contra" + msgFormat, A[i], "<:", B[i]);
            AddAssignableConstraint(tok, B[i], A[i], em);
            moreXConstraints = true;
          } else {
            var em = new TypeConstraint.ErrorMsgWithBase(errMsg, "non" + msgFormat, A[i], "=", B[i]);
            ConstrainSubtypeRelation_Equal(A[i], B[i], em);
          }
        }
      }
    }

    /// <summary>
    /// Adds the subtyping constraint that "a" and "b" are the same type.
    /// </summary>
    private void ConstrainSubtypeRelation_Equal(Type a, Type b, TypeConstraint.ErrorMsg errMsg) {
      Contract.Requires(a != null);
      Contract.Requires(b != null);
      Contract.Requires(errMsg != null);

      var proxy = a.Normalize() as TypeProxy;
      if (proxy != null && proxy.T == null && !Reaches(b, proxy, 1, new HashSet<TypeProxy>())) {
        if (DafnyOptions.O.TypeInferenceDebug) {
          Console.WriteLine("DEBUG: (invariance) assigning proxy {0}.T := {1}", proxy, b);
        }
        proxy.T = b;
      }
      proxy = b.Normalize() as TypeProxy;
      if (proxy != null && proxy.T == null && !Reaches(a, proxy, 1, new HashSet<TypeProxy>())) {
        if (DafnyOptions.O.TypeInferenceDebug) {
          Console.WriteLine("DEBUG: (invariance) assigning proxy {0}.T := {1}", proxy, a);
        }
        proxy.T = a;
      }

      ConstrainSubtypeRelation(a, b, errMsg, true);
      ConstrainSubtypeRelation(b, a, errMsg, true);
    }

    /// <summary>
    /// Adds the subtyping constraint that "sub" is a subtype of "super".
    /// If this constraint seems feasible, returns "true".  Otherwise, prints error message (either "errMsg" or something
    /// more specific) and returns "false".
    /// Note, if in doubt, this method can return "true", because the constraints will be checked for sure at a later stage.
    /// </summary>
    private bool ConstrainSubtypeRelation(Type super, Type sub, TypeConstraint.ErrorMsg errMsg, bool keepConstraints = false, bool allowDecisions = false) {
      Contract.Requires(sub != null);
      Contract.Requires(super != null);
      Contract.Requires(errMsg != null);

      if (!keepConstraints && super is InferredTypeProxy) {
        var ip = (InferredTypeProxy)super;
        if (ip.KeepConstraints) {
          keepConstraints = true;
        }
      }
      if (!keepConstraints && sub is InferredTypeProxy) {
        var ip = (InferredTypeProxy)sub;
        if (ip.KeepConstraints) {
          keepConstraints = true;
        }
      }

      super = super.NormalizeExpand(keepConstraints);
      sub = sub.NormalizeExpand(keepConstraints);
      var c = new TypeConstraint(super, sub, errMsg, keepConstraints);
      AllTypeConstraints.Add(c);
      return ConstrainSubtypeRelation_Aux(super, sub, c, keepConstraints, allowDecisions);
    }
    private bool ConstrainSubtypeRelation_Aux(Type super, Type sub, TypeConstraint c, bool keepConstraints, bool allowDecisions) {
      Contract.Requires(sub != null);
      Contract.Requires(!(sub is TypeProxy) || ((TypeProxy)sub).T == null);  // caller is expected to have Normalized away proxies
      Contract.Requires(super != null);
      Contract.Requires(!(super is TypeProxy) || ((TypeProxy)super).T == null);  // caller is expected to have Normalized away proxies
      Contract.Requires(c != null);

      if (object.ReferenceEquals(super, sub)) {
        return true;
      } else if (super is TypeProxy && sub is TypeProxy) {
        // both are proxies
        ((TypeProxy)sub).AddSupertype(c);
        ((TypeProxy)super).AddSubtype(c);
        return true;
      } else if (sub is TypeProxy) {
        var proxy = (TypeProxy)sub;
        proxy.AddSupertype(c);
        AssignKnownEnd(proxy, keepConstraints, allowDecisions);
        return true;
      } else if (super is TypeProxy) {
        var proxy = (TypeProxy)super;
        proxy.AddSubtype(c);
        AssignKnownEnd(proxy, keepConstraints, allowDecisions);
        return true;
      } else {
        // two non-proxy types
        // set "headSymbolsAgree" to "false" if it's clear the head symbols couldn't be the same; "true" means they may be the same
        bool headSymbolsAgree = Type.IsHeadSupertypeOf(super.NormalizeExpand(keepConstraints), sub);
        if (!headSymbolsAgree) {
          c.FlagAsError(this);
          return false;
        }
        // TODO: inspect type parameters in order to produce some error messages sooner
        return true;
      }
    }

    /// <summary>
    /// "root" says that the type is a non-artificial type (that is, not an ArtificialType) with no proper supertypes.
    /// "leaf" says that the only possible proper subtypes are subset types of the type. Thus, the only
    /// types that are not leaf types are traits and artificial types.
    /// The "headIs" versions speak only about the head symbols, so it is possible that the given
    /// type arguments would change the root/leaf status of the entire type.
    /// </summary>
    void DetermineRootLeaf(Type t, out bool isRoot, out bool isLeaf, out bool headIsRoot, out bool headIsLeaf) {
      Contract.Requires(t != null);
      Contract.Ensures(!Contract.ValueAtReturn(out isRoot) || Contract.ValueAtReturn(out headIsRoot)); // isRoot ==> headIsRoot
      Contract.Ensures(!Contract.ValueAtReturn(out isLeaf) || Contract.ValueAtReturn(out headIsLeaf)); // isLeaf ==> headIsLeaf
      t = t.NormalizeExpandKeepConstraints();
      if (t.IsObjectQ) {
        isRoot = true; isLeaf = false;
        headIsRoot = true; headIsLeaf = false;
      } else if (t is ArrowType) {
        var arr = (ArrowType)t;
        headIsRoot = true; headIsLeaf = true;  // these are definitely true
        isRoot = true; isLeaf = true;  // set these to true until proven otherwise
        Contract.Assert(arr.Arity + 1 == arr.TypeArgs.Count);
        for (int i = 0; i < arr.TypeArgs.Count; i++) {
          var arg = arr.TypeArgs[i];
          DetermineRootLeaf(arg, out var r, out var l, out _, out _);
          if (i < arr.Arity) {
            isRoot &= l; isLeaf &= r;  // argument types are contravariant
          } else {
            isRoot &= r; isLeaf &= l;  // result type is covariant
          }
        }
      } else if (t is UserDefinedType) {
        var udt = (UserDefinedType)t;
        var cl = udt.ResolvedClass;
        if (cl != null) {
          if (cl is TypeParameter) {
            var tp = udt.AsTypeParameter;
            Contract.Assert(tp != null);
            headIsRoot = true; headIsLeaf = true;  // all type parameters are non-variant
          } else if (cl is SubsetTypeDecl) {
            headIsRoot = false; headIsLeaf = true;
          } else if (cl is NewtypeDecl) {
            headIsRoot = true; headIsLeaf = true;
          } else if (cl is TraitDecl) {
            headIsRoot = false; headIsLeaf = false;
          } else if (cl is ClassDecl) {
            headIsRoot = false; headIsLeaf = true;
          } else if (cl is OpaqueTypeDecl) {
            headIsRoot = true; headIsLeaf = true;
          } else if (cl is InternalTypeSynonymDecl) {
            Contract.Assert(object.ReferenceEquals(t, t.NormalizeExpand())); // should be opaque in scope
            headIsRoot = true; headIsLeaf = true;
          } else {
            Contract.Assert(cl is DatatypeDecl);
            headIsRoot = true; headIsLeaf = true;
          }
          // for "isRoot" and "isLeaf", also take into consideration the root/leaf status of type arguments
          isRoot = headIsRoot; isLeaf = headIsLeaf;
          Contract.Assert(udt.TypeArgs.Count == cl.TypeArgs.Count);
          for (int i = 0; i < udt.TypeArgs.Count; i++) {
            var variance = cl.TypeArgs[i].Variance;
            if (variance != TypeParameter.TPVariance.Non) {
              DetermineRootLeaf(udt.TypeArgs[i], out var r, out var l, out _, out _);
              // isRoot and isLeaf aren't duals, so Co and Contra require separate consideration beyond inversion.
              switch (variance) {
                case TypeParameter.TPVariance.Co: { isRoot &= r; isLeaf &= l; break; }
                // A invariably constructible subtype becomes a supertype, and thus the enclosing type is never a root.
                case TypeParameter.TPVariance.Contra: { isRoot &= false; isLeaf &= r; break; }
              }
            }
          }
        } else {
          isRoot = false; isLeaf = false;  // don't know
          headIsRoot = false; headIsLeaf = false;
        }
      } else if (t.IsBoolType || t.IsCharType || t.IsIntegerType || t.IsRealType || t.AsNewtype != null || t.IsBitVectorType || t.IsBigOrdinalType) {
        isRoot = true; isLeaf = true;
        headIsRoot = true; headIsLeaf = true;
      } else if (t is ArtificialType) {
        isRoot = false; isLeaf = false;
        headIsRoot = false; headIsLeaf = false;
      } else if (t is MapType) {  // map, imap
        Contract.Assert(t.TypeArgs.Count == 2);
        DetermineRootLeaf(t.TypeArgs[0], out var r0, out _, out _, out _);
        DetermineRootLeaf(t.TypeArgs[1], out var r1, out _, out _, out _);
        isRoot = r0 & r1; isLeaf = r0 & r1;  // map types are covariant in both type arguments
        headIsRoot = true; headIsLeaf = true;
      } else if (t is CollectionType) {  // set, iset, multiset, seq
        Contract.Assert(t.TypeArgs.Count == 1);
        DetermineRootLeaf(t.TypeArgs[0], out isRoot, out isLeaf, out _, out _);  // type is covariant is type argument
        headIsRoot = true; headIsLeaf = true;
      } else {
        isRoot = false; isLeaf = false;  // don't know
        headIsRoot = false; headIsLeaf = false;
      }
    }

    int _recursionDepth = 0;
    private bool AssignProxyAndHandleItsConstraints(TypeProxy proxy, Type t, bool keepConstraints = false) {
      Contract.Requires(proxy != null);
      Contract.Requires(proxy.T == null);
      Contract.Requires(t != null);
      Contract.Requires(!(t is TypeProxy));
      Contract.Requires(!(t is ArtificialType));
      if (_recursionDepth == 20000) {
        Contract.Assume(false);  // possible infinite recursion
      }
      _recursionDepth++;
      var b = AssignProxyAndHandleItsConstraints_aux(proxy, t, keepConstraints);
      _recursionDepth--;
      return b;
    }
    /// <summary>
    /// This method is called if "proxy" is an unassigned proxy and "t" is a type whose head symbol is known.
    /// It always sets "proxy.T" to "t".
    /// Then, it deals with the constraints of "proxy" as follows:
    /// * If the constraint compares "t" with a non-proxy with a head comparable with that of "t",
    ///   then add constraints that the type arguments satisfy the desired subtyping constraint
    /// * If the constraint compares "t" with a non-proxy with a head not comparable with that of "t",
    ///   then report an error
    /// * If the constraint compares "t" with a proxy, then (depending on the constraint and "t") attempt
    ///   to recursively set it
    /// After this process, the proxy's .Supertypes and .Subtypes lists of constraints are no longer needed.
    /// If anything is found to be infeasible, "false" is returned (and the propagation may be interrupted);
    /// otherwise, "true" is returned.
    /// </summary>
    private bool AssignProxyAndHandleItsConstraints_aux(TypeProxy proxy, Type t, bool keepConstraints = false) {
      Contract.Requires(proxy != null);
      Contract.Requires(proxy.T == null);
      Contract.Requires(t != null);
      Contract.Requires(!(t is TypeProxy));
      Contract.Requires(!(t is ArtificialType));

      t = keepConstraints ? t.Normalize() : t.NormalizeExpand();
      // never violate the type constraint of a literal expression
      var followedRequestedAssignment = true;
      foreach (var su in proxy.Supertypes) {
        if (su is IntVarietiesSupertype) {
          var fam = TypeProxy.GetFamily(t);
          if (fam == TypeProxy.Family.IntLike || fam == TypeProxy.Family.BitVector || fam == TypeProxy.Family.Ordinal) {
            // good, let's continue with the request to equate the proxy with t
            // unless...
            if (t != t.NormalizeExpand()) {
              // force the type to be a base type
              if (DafnyOptions.O.TypeInferenceDebug) {
                Console.WriteLine("DEBUG: hijacking {0}.T := {1} to instead assign {2}", proxy, t, t.NormalizeExpand());
              }
              t = t.NormalizeExpand();
              followedRequestedAssignment = false;
            }
          } else {
            // hijack the setting of proxy; to do that, we decide on a particular int variety now
            if (DafnyOptions.O.TypeInferenceDebug) {
              Console.WriteLine("DEBUG: hijacking {0}.T := {1} to instead assign {2}", proxy, t, Type.Int);
            }
            t = Type.Int;
            followedRequestedAssignment = false;
          }
          break;
        } else if (su is RealVarietiesSupertype) {
          if (TypeProxy.GetFamily(t) == TypeProxy.Family.RealLike) {
            // good, let's continue with the request to equate the proxy with t
            // unless...
            if (t != t.NormalizeExpand()) {
              // force the type to be a base type
              if (DafnyOptions.O.TypeInferenceDebug) {
                Console.WriteLine("DEBUG: hijacking {0}.T := {1} to instead assign {2}", proxy, t, t.NormalizeExpand());
              }
              t = t.NormalizeExpand();
              followedRequestedAssignment = false;
            }
          } else {
            // hijack the setting of proxy; to do that, we decide on a particular real variety now
            if (DafnyOptions.O.TypeInferenceDebug) {
              Console.WriteLine("DEBUG: hijacking {0}.T := {1} to instead assign {2}", proxy, t, Type.Real);
            }
            t = Type.Real;
            followedRequestedAssignment = false;
          }
          break;
        }
      }
      // set proxy.T right away, so that we can freely recurse without having to worry about infinite recursion
      if (DafnyOptions.O.TypeInferenceDebug) {
        Console.WriteLine("DEBUG: setting proxy {0}.T := {1}", proxy, t);
      }
      proxy.T = t;

      // check feasibility
      DetermineRootLeaf(t, out var isRoot, out var isLeaf, out _, out _);
      // propagate up
      foreach (var c in proxy.SupertypeConstraints) {
        var u = keepConstraints ? c.Super.NormalizeExpandKeepConstraints() : c.Super.NormalizeExpand();
        if (!(u is TypeProxy)) {
          ImposeSubtypingConstraint(u, t, c.ErrMsg);
        } else if (isRoot) {
          // If t is a root, we might as well constrain u now.  Otherwise, we'll wait until the .Subtype constraint of u is dealt with.
          AssignProxyAndHandleItsConstraints((TypeProxy)u, t, keepConstraints);
        }
      }
      // propagate down
      foreach (var c in proxy.SubtypeConstraints) {
        var u = keepConstraints ? c.Sub.NormalizeExpandKeepConstraints() : c.Sub.NormalizeExpand();
        Contract.Assert(!TypeProxy.IsSupertypeOfLiteral(u));  // these should only appear among .Supertypes
        if (!(u is TypeProxy)) {
          ImposeSubtypingConstraint(t, u, c.ErrMsg);
        } else if (isLeaf) {
          // If t is a leaf (no pun intended), we might as well constrain u now.  Otherwise, we'll wait until the .Supertype constraint of u is dealt with.
          AssignProxyAndHandleItsConstraints((TypeProxy)u, t, keepConstraints);
        }
      }

      return followedRequestedAssignment;
    }

    /// <summary>
    /// Impose constraints that "sub" is a subtype of "super", returning "false" if this leads to an overconstrained situation.
    /// In most cases, "sub" being a subtype of "super" means that "sub" and "super" have the same head symbol and, therefore, the
    /// same number of type arguments. Depending on the polarities of the type parameters, the corresponding arguments
    /// of "sub" and "super" must be in co-, in-, or contra-variant relationships to each other.
    /// There are two ways "sub" can be a subtype of "super" without the two having the same head symbol.
    /// One way is that "sub" is a subset type. In this case, the method starts by moving "sub" up toward "super".
    /// The other way is that "super" is a trait (possibly
    /// the trait "object").  By a current restriction in Dafny's type system, traits have no type parameters, so in this case, it
    /// suffices to check that the head symbol of "super" is something that derives from "sub".
    /// </summary>
    private bool ImposeSubtypingConstraint(Type super, Type sub, TypeConstraint.ErrorMsg errorMsg) {
      Contract.Requires(super != null && !(super is TypeProxy));
      Contract.Requires(sub != null && !(sub is TypeProxy));
      Contract.Requires(errorMsg != null);
      super = super.NormalizeExpandKeepConstraints();
      sub = sub.NormalizeExpandKeepConstraints();
      List<int> polarities = ConstrainTypeHead_Recursive(super, ref sub);
      if (polarities == null) {
        errorMsg.FlagAsError(this);
        return false;
      }
      bool keepConstraints = KeepConstraints(super, sub);
      var p = polarities.Count;
      Contract.Assert(p == super.TypeArgs.Count);  // postcondition of ConstrainTypeHead
      Contract.Assert(p == 0 || sub.TypeArgs.Count == super.TypeArgs.Count);  // postcondition of ConstrainTypeHead
      for (int i = 0; i < p; i++) {
        var pol = polarities[i];
        var tp = p == 1 ? "" : " " + i;
        var errMsg = new TypeConstraint.ErrorMsgWithBase(errorMsg,
          pol < 0 ? "contravariant type parameter{0} would require {1} <: {2}" :
          pol > 0 ? "covariant type parameter{0} would require {2} <: {1}" :
          "non-variant type parameter{0} would require {1} = {2}",
          tp, super.TypeArgs[i], sub.TypeArgs[i]);
        if (pol >= 0) {
          if (!ConstrainSubtypeRelation(super.TypeArgs[i], sub.TypeArgs[i], errMsg, keepConstraints)) {
            return false;
          }
        }
        if (pol <= 0) {
          if (!ConstrainSubtypeRelation(sub.TypeArgs[i], super.TypeArgs[i], errMsg, keepConstraints)) {
            return false;
          }
        }
      }
      return true;
    }

    /// <summary>
    /// This is a more liberal version of "ConstrainTypeHead" below. It is willing to move "sub"
    /// upward toward its parents until it finds a head that matches "super", if any.
    /// </summary>
    private static List<int> ConstrainTypeHead_Recursive(Type super, ref Type sub) {
      Contract.Requires(super != null);
      Contract.Requires(sub != null);

      super = super.NormalizeExpandKeepConstraints();
      sub = sub.NormalizeExpandKeepConstraints();

      var polarities = ConstrainTypeHead(super, sub);
      if (polarities != null) {
        return polarities;
      }

      foreach (var subParentType in sub.ParentTypes()) {
        sub = subParentType;
        polarities = ConstrainTypeHead_Recursive(super, ref sub);
        if (polarities != null) {
          return polarities;
        }
      }

      return null;
    }

    /// <summary>
    /// Determines if the head of "sub" can be a subtype of "super".
    /// If this is not possible, null is returned.
    /// If it is possible, return a list of polarities, one for each type argument of "sub".  Polarities
    /// indicate:
    ///     +1  co-variant
    ///      0  invariant
    ///     -1  contra-variant
    /// "sub" is of some type that can (in general) have type parameters.
    /// See also note about Dafny's current type system in the description of method "ImposeSubtypingConstraint".
    /// </summary>
    private static List<int> ConstrainTypeHead(Type super, Type sub) {
      Contract.Requires(super != null && !(super is TypeProxy));
      Contract.Requires(sub != null && !(sub is TypeProxy));
      if (super is IntVarietiesSupertype) {
        var famSub = TypeProxy.GetFamily(sub);
        if (famSub == TypeProxy.Family.IntLike || famSub == TypeProxy.Family.BitVector || famSub == TypeProxy.Family.Ordinal || super.Equals(sub)) {
          return new List<int>();
        } else {
          return null;
        }
      } else if (super is RealVarietiesSupertype) {
        if (TypeProxy.GetFamily(sub) == TypeProxy.Family.RealLike || super.Equals(sub)) {
          return new List<int>();
        } else {
          return null;
        }
      }
      switch (TypeProxy.GetFamily(super)) {
        case TypeProxy.Family.Bool:
        case TypeProxy.Family.Char:
        case TypeProxy.Family.IntLike:
        case TypeProxy.Family.RealLike:
        case TypeProxy.Family.Ordinal:
        case TypeProxy.Family.BitVector:
          if (super.Equals(sub)) {
            return new List<int>();
          } else {
            return null;
          }
        case TypeProxy.Family.ValueType:
        case TypeProxy.Family.Ref:
        case TypeProxy.Family.Opaque:
          break;  // more elaborate work below
        case TypeProxy.Family.Unknown:
          return null;
        default:
          Contract.Assert(false);  // unexpected type (the precondition of ConstrainTypeHead says "no proxies")
          return null;  // please compiler
      }
      if (super is SetType) {
        var tt = (SetType)super;
        var uu = sub as SetType;
        return uu != null && tt.Finite == uu.Finite ? new List<int> { 1 } : null;
      } else if (super is SeqType) {
        return sub is SeqType ? new List<int> { 1 } : null;
      } else if (super is MultiSetType) {
        return sub is MultiSetType ? new List<int> { 1 } : null;
      } else if (super is MapType) {
        var tt = (MapType)super;
        var uu = sub as MapType;
        return uu != null && tt.Finite == uu.Finite ? new List<int> { 1, 1 } : null;
      } else if (super.IsObjectQ) {
        return sub.IsRefType ? new List<int>() : null;
      } else {
        // The only remaining cases are that "super" is a (co)datatype, opaque type, or non-object trait/class.
        // In each of these cases, "super" is a UserDefinedType.
        var udfSuper = (UserDefinedType)super;
        var clSuper = udfSuper.ResolvedClass;
        if (clSuper == null) {
          Contract.Assert(super.TypeArgs.Count == 0);
          if (super.IsTypeParameter) {
            // we're looking at a type parameter
            return super.AsTypeParameter == sub.AsTypeParameter ? new List<int>() : null;
          } else {
            Contract.Assert(super.IsInternalTypeSynonym);
            return super.AsInternalTypeSynonym == sub.AsInternalTypeSynonym ? new List<int>() : null;
          }
        }
        var udfSub = sub as UserDefinedType;
        var clSub = udfSub == null ? null : udfSub.ResolvedClass;
        if (clSub == null) {
          return null;
        } else if (clSuper == clSub) {
          // good
          var polarities = new List<int>();
          Contract.Assert(clSuper.TypeArgs.Count == udfSuper.TypeArgs.Count);
          Contract.Assert(clSuper.TypeArgs.Count == udfSub.TypeArgs.Count);
          foreach (var tp in clSuper.TypeArgs) {
            var polarity = TypeParameter.Direction(tp.Variance);
            polarities.Add(polarity);
          }

          return polarities;
        } else if (udfSub.IsRefType && super.IsObjectQ) {
          return new List<int>();
        } else if (udfSub.IsNonNullRefType && super.IsObject) {
          return new List<int>();
        } else {
          return null;
        }
      }
    }
    private static bool KeepConstraints(Type super, Type sub) {
      Contract.Requires(super != null && !(super is TypeProxy));
      Contract.Requires(sub != null && !(sub is TypeProxy));
      if (super is IntVarietiesSupertype) {
        return false;
      } else if (super is RealVarietiesSupertype) {
        return false;
      }
      switch (TypeProxy.GetFamily(super)) {
        case TypeProxy.Family.Bool:
        case TypeProxy.Family.Char:
        case TypeProxy.Family.IntLike:
        case TypeProxy.Family.RealLike:
        case TypeProxy.Family.Ordinal:
        case TypeProxy.Family.BitVector:
          return false;
        case TypeProxy.Family.ValueType:
        case TypeProxy.Family.Ref:
        case TypeProxy.Family.Opaque:
          break;  // more elaborate work below
        case TypeProxy.Family.Unknown:
          return false;
      }
      if (super is SetType || super is SeqType || super is MultiSetType || super is MapType) {
        return true;
      } else if (super is ArrowType) {
        return false;
      } else if (super.IsObjectQ) {
        return false;
      } else {
        // super is UserDefinedType
        return true;
      }
    }

    public List<TypeConstraint> AllTypeConstraints = new List<TypeConstraint>();
    public List<XConstraint> AllXConstraints = new List<XConstraint>();

    public class XConstraint {
      public readonly IToken tok;
      public readonly string ConstraintName;
      public readonly Type[] Types;
      public readonly TypeConstraint.ErrorMsg errorMsg;
      public XConstraint(IToken tok, string constraintName, Type[] types, TypeConstraint.ErrorMsg errMsg) {
        Contract.Requires(tok != null);
        Contract.Requires(constraintName != null);
        Contract.Requires(types != null);
        Contract.Requires(errMsg != null);
        this.tok = tok;
        ConstraintName = constraintName;
        Types = types;
        errorMsg = errMsg;
      }

      public override string ToString() {
        var s = ConstraintName + ":";
        foreach (var t in Types) {
          s += " " + t;
        }
        return s;
      }

      /// <summary>
      /// Tries to confirm the XConstraint.
      /// If the XConstraint can be confirmed, or at least is plausible enough to have been converted into other type
      /// constraints or more XConstraints, then "true" is returned and the out-parameters "convertedIntoOtherTypeConstraints"
      /// and "moreXConstraints" are set to true accordingly.
      /// If the XConstraint can be refuted, then an error message will be produced and "true" is returned (to indicate
      /// that this XConstraint has finished serving its purpose).
      /// If there's not enough information to confirm or refute the XConstraint, then "false" is returned.
      /// </summary>
      public bool Confirm(Resolver resolver, bool fullstrength, out bool convertedIntoOtherTypeConstraints, out bool moreXConstraints) {
        Contract.Requires(resolver != null);
        convertedIntoOtherTypeConstraints = false;
        moreXConstraints = false;
        var t = Types[0].NormalizeExpand();
        if (t is TypeProxy) {
          switch (ConstraintName) {
            case "Assignable":
            case "Equatable":
            case "EquatableArg":
            case "Indexable":
            case "Innable":
            case "MultiIndexable":
            case "IntOrORDINAL":
              // have a go downstairs
              break;
            default:
              return false;  // there's not enough information to confirm or refute this XConstraint
          }
        }
        bool satisfied;
        Type tUp, uUp;
        switch (ConstraintName) {
          case "Assignable": {
              Contract.Assert(t == t.Normalize());  // it's already been normalized above
              var u = Types[1].NormalizeExpand();
              if (CheckTypeInferenceVisitor.IsDetermined(t) &&
                  (fullstrength
                   || !ProxyWithNoSubTypeConstraint(u, resolver)
                   || (u is TypeProxy
                       && Types[0].NormalizeExpandKeepConstraints() is var t0constrained
                       && (t0constrained.IsNonNullRefType || t0constrained.AsSubsetType != null)
                       && resolver.HasApplicableNullableRefTypeConstraint(new HashSet<TypeProxy>() { (TypeProxy)u })))) {
                // This is the best case.  We convert Assignable(t, u) to the subtype constraint base(t) :> u.
                if (CheckTypeInferenceVisitor.IsDetermined(u) && t.IsSubtypeOf(u, false, true) && t.IsRefType) {
                  // But we also allow cases where the rhs is a proper supertype of the lhs, and let the verifier
                  // determine whether the rhs is provably an instance of the lhs.
                  resolver.ConstrainAssignable((NonProxyType)u, (NonProxyType)t, errorMsg, out moreXConstraints, fullstrength);
                } else {
                  resolver.ConstrainAssignable((NonProxyType)t, u, errorMsg, out moreXConstraints, fullstrength);
                }
                convertedIntoOtherTypeConstraints = true;
                return true;
              } else if (u.IsTypeParameter) {
                // we need the constraint base(t) :> u, which for a type parameter t can happen iff t :> u
                resolver.ConstrainSubtypeRelation(t, u, errorMsg);
                convertedIntoOtherTypeConstraints = true;
                return true;
              } else if (Type.FromSameHead(t, u, out tUp, out uUp)) {
                resolver.ConstrainAssignableTypeArgs(tUp, tUp.TypeArgs, uUp.TypeArgs, errorMsg, out moreXConstraints);
                return true;
              } else if (fullstrength && t is NonProxyType) {
                // We convert Assignable(t, u) to the subtype constraint base(t) :> u.
                resolver.ConstrainAssignable((NonProxyType)t, u, errorMsg, out moreXConstraints, fullstrength);
                convertedIntoOtherTypeConstraints = true;
                return true;
              } else if (fullstrength && u is NonProxyType) {
                // We're willing to change "base(t) :> u" to the stronger constraint "t :> u" for the sake of making progress.
                resolver.ConstrainSubtypeRelation(t, u, errorMsg);
                convertedIntoOtherTypeConstraints = true;
                return true;
              }
              // There's not enough information to say anything
              return false;
            }
          case "NumericType":
            satisfied = t.IsNumericBased();
            break;
          case "IntegerType":
            satisfied = t.IsNumericBased(Type.NumericPersuasion.Int);
            break;
          case "IsBitvector":
            satisfied = t.IsBitVectorType;
            break;
          case "IsRefType":
            satisfied = t.IsRefType;
            break;
          case "IsNullableRefType":
            satisfied = t.IsRefType && !t.IsNonNullRefType;
            break;
          case "Orderable_Lt":
            satisfied = t.IsNumericBased() || t.IsBitVectorType || t.IsBigOrdinalType || t.IsCharType || t is SeqType || t is SetType || t is MultiSetType;
            break;
          case "Orderable_Gt":
            satisfied = t.IsNumericBased() || t.IsBitVectorType || t.IsBigOrdinalType || t.IsCharType || t is SetType || t is MultiSetType;
            break;
          case "RankOrderable": {
              var u = Types[1].NormalizeExpand();
              if (u is TypeProxy) {
                return false;  // not enough information
              }
              satisfied = (t.IsIndDatatype || t.IsTypeParameter) && u.IsIndDatatype;
              break;
            }
          case "Plussable":
            satisfied = t.IsNumericBased() || t.IsBitVectorType || t.IsBigOrdinalType || t.IsCharType || t is SeqType || t is SetType || t is MultiSetType || t is MapType;
            break;
          case "Minusable":
            satisfied = t.IsNumericBased() || t.IsBitVectorType || t.IsBigOrdinalType || t.IsCharType || t is SetType || t is MultiSetType || t is MapType;
            break;
          case "Mullable":
            satisfied = t.IsNumericBased() || t.IsBitVectorType || t is SetType || t is MultiSetType;
            break;
          case "IntOrORDINAL":
            if (!(t is TypeProxy)) {
              if (TernaryExpr.PrefixEqUsesNat) {
                satisfied = t.IsNumericBased(Type.NumericPersuasion.Int);
              } else {
                satisfied = t.IsNumericBased(Type.NumericPersuasion.Int) || t.IsBigOrdinalType;
              }
            } else if (fullstrength) {
              var proxy = (TypeProxy)t;
              if (TernaryExpr.PrefixEqUsesNat) {
                resolver.AssignProxyAndHandleItsConstraints(proxy, Type.Int);
              } else {
                // let's choose ORDINAL over int
                resolver.AssignProxyAndHandleItsConstraints(proxy, Type.BigOrdinal);
              }
              convertedIntoOtherTypeConstraints = true;
              satisfied = true;
            } else {
              return false;
            }
            break;
          case "NumericOrBitvector":
            satisfied = t.IsNumericBased() || t.IsBitVectorType;
            break;
          case "NumericOrBitvectorOrCharOrORDINAL":
            satisfied = t.IsNumericBased() || t.IsBitVectorType || t.IsCharType || t.IsBigOrdinalType;
            break;
          case "IntLikeOrBitvector":
            satisfied = t.IsNumericBased(Type.NumericPersuasion.Int) || t.IsBitVectorType;
            break;
          case "BooleanBits":
            satisfied = t.IsBoolType || t.IsBitVectorType;
            break;
          case "Sizeable":
            satisfied = (t is SetType && ((SetType)t).Finite) || t is MultiSetType || t is SeqType || (t is MapType && ((MapType)t).Finite);
            break;
          case "Disjointable":
            satisfied = t is SetType || t is MultiSetType;
            break;
          case "MultiSetConvertible":
            satisfied = (t is SetType && ((SetType)t).Finite) || t is SeqType;
            if (satisfied) {
              Type elementType = ((CollectionType)t).Arg;
              var u = Types[1];  // note, it's okay if "u" is a TypeProxy
              var em = new TypeConstraint.ErrorMsgWithBase(errorMsg, "expecting element type {0} (got {1})", u, elementType);
              resolver.ConstrainSubtypeRelation_Equal(elementType, u, em);
              convertedIntoOtherTypeConstraints = true;
            }
            break;
          case "IsCoDatatype":
            satisfied = t.IsCoDatatype;
            break;
          case "Indexable":
            if (!(t is TypeProxy)) {
              satisfied = t is SeqType || t is MultiSetType || t is MapType || (t.IsArrayType && t.AsArrayType.Dims == 1);
            } else {
              // t is a proxy, but perhaps it stands for something between "object" and "array<?>".  If so, we can add a constraint
              // that it does have the form "array<?>", since "object" would not be Indexable.
              var proxy = (TypeProxy)t;
              Type join = null;
              if (resolver.JoinOfAllSubtypes(proxy, ref join, new HashSet<TypeProxy>()) && join != null) {
                var headWithProxyArgs = Type.HeadWithProxyArgs(join);
                var tt = headWithProxyArgs.NormalizeExpand();
                satisfied = tt is SeqType || tt is MultiSetType || tt is MapType || (tt.IsArrayType && tt.AsArrayType.Dims == 1);
                if (satisfied) {
                  resolver.AssignProxyAndHandleItsConstraints(proxy, headWithProxyArgs, true);
                  convertedIntoOtherTypeConstraints = true;
                }
              } else {
                return false;  // we can't determine the answer
              }
            }
            break;
          case "MultiIndexable":
            if (!(t is TypeProxy)) {
              satisfied = t is SeqType || (t.IsArrayType && t.AsArrayType.Dims == 1);
            } else {
              // t is a proxy, but perhaps it stands for something between "object" and "array<?>".  If so, we can add a constraint
              // that it does have the form "array<?>", since "object" would not be Indexable.
              var proxy = (TypeProxy)t;
              Type join = null;
              if (resolver.JoinOfAllSubtypes(proxy, ref join, new HashSet<TypeProxy>()) && join != null) {
                var headWithProxyArgs = Type.HeadWithProxyArgs(join);
                var tt = headWithProxyArgs.NormalizeExpand();
                satisfied = tt is SeqType || (tt.IsArrayType && tt.AsArrayType.Dims == 1);
                if (satisfied) {
                  resolver.AssignProxyAndHandleItsConstraints(proxy, headWithProxyArgs, true);
                  convertedIntoOtherTypeConstraints = true;
                }
              } else {
                return false;  // we can't determine the answer
              }
            }
            break;
          case "Innable": {
              var elementType = FindCollectionType(t, true, new HashSet<TypeProxy>()) ?? FindCollectionType(t, false, new HashSet<TypeProxy>());
              if (elementType != null) {
                var u = Types[1];  // note, it's okay if "u" is a TypeProxy
                resolver.AddXConstraint(this.tok, "Equatable", elementType, u, new TypeConstraint.ErrorMsgWithBase(errorMsg, "expecting element type to be assignable to {1} (got {0})", u, elementType));
                moreXConstraints = true;
                return true;
              }
              if (t is TypeProxy) {
                return false;  // not enough information to do anything
              }
              satisfied = false;
              break;
            }
          case "SeqUpdatable": {
              var xcWithExprs = (XConstraintWithExprs)this;
              var index = xcWithExprs.Exprs[0];
              var value = xcWithExprs.Exprs[1];
              if (t is SeqType) {
                var s = (SeqType)t;
                resolver.ConstrainToIntegerType(index, true, "sequence update requires integer- or bitvector-based index (got {0})");
                resolver.ConstrainSubtypeRelation(s.Arg, value.Type, value, "sequence update requires the value to have the element type of the sequence (got {0})", value.Type);
              } else if (t is MapType) {
                var s = (MapType)t;
                if (s.Finite) {
                  resolver.ConstrainSubtypeRelation(s.Domain, index.Type, index, "map update requires domain element to be of type {0} (got {1})", s.Domain, index.Type);
                  resolver.ConstrainSubtypeRelation(s.Range, value.Type, value, "map update requires the value to have the range type {0} (got {1})", s.Range, value.Type);
                } else {
                  resolver.ConstrainSubtypeRelation(s.Domain, index.Type, index, "imap update requires domain element to be of type {0} (got {1})", s.Domain, index.Type);
                  resolver.ConstrainSubtypeRelation(s.Range, value.Type, value, "imap update requires the value to have the range type {0} (got {1})", s.Range, value.Type);
                }
              } else if (t is MultiSetType) {
                var s = (MultiSetType)t;
                resolver.ConstrainSubtypeRelation(s.Arg, index.Type, index, "multiset update requires domain element to be of type {0} (got {1})", s.Arg, index.Type);
                resolver.ConstrainToIntegerType(value, false, "multiset update requires integer-based numeric value (got {0})");
              } else {
                satisfied = false;
                break;
              }
              convertedIntoOtherTypeConstraints = true;
              return true;
            }
          case "ContainerIndex":
            // The semantics of this XConstraint is that *if* the head is seq/array/map/multiset, then its element/domain type must a supertype of "u"
            Type indexType;
            if (t is SeqType || t.IsArrayType) {
              resolver.ConstrainToIntegerType(errorMsg.Tok, Types[1], true, errorMsg);
              convertedIntoOtherTypeConstraints = true;
              return true;
            } else if (t is MapType) {
              indexType = ((MapType)t).Domain;
            } else if (t is MultiSetType) {
              indexType = ((MultiSetType)t).Arg;
            } else {
              // some other head symbol; that's cool
              return true;
            }
            // note, it's okay if "Types[1]" is a TypeProxy
            resolver.ConstrainSubtypeRelation(indexType, Types[1], errorMsg);  // use the same error message
            convertedIntoOtherTypeConstraints = true;
            return true;
          case "ContainerResult":
            // The semantics of this XConstraint is that *if* the head is seq/array/map/multiset, then the type of a selection must a subtype of "u"
            Type resultType;
            if (t is SeqType) {
              resultType = ((SeqType)t).Arg;
            } else if (t.IsArrayType) {
              resultType = UserDefinedType.ArrayElementType(t);
            } else if (t is MapType) {
              resultType = ((MapType)t).Range;
            } else if (t is MultiSetType) {
              resultType = resolver.builtIns.Nat();
            } else {
              // some other head symbol; that's cool
              return true;
            }
            // note, it's okay if "Types[1]" is a TypeProxy
            resolver.ConstrainSubtypeRelation(Types[1], resultType, errorMsg);
            convertedIntoOtherTypeConstraints = true;
            return true;
          case "Equatable": {
              t = Types[0].NormalizeExpandKeepConstraints();
              var u = Types[1].NormalizeExpandKeepConstraints();
              if (object.ReferenceEquals(t, u)) {
                return true;
              }
              if (t is TypeProxy && u is TypeProxy) {
                return false;  // not enough information to do anything sensible
              } else if (t is TypeProxy || u is TypeProxy) {
                TypeProxy proxy;
                Type other;
                if (t is TypeProxy) {
                  proxy = (TypeProxy)t;
                  other = u;
                } else {
                  proxy = (TypeProxy)u;
                  other = t;
                }
                if (other.IsNumericBased() || other.IsBitVectorType || other.IsBigOrdinalType) {
                  resolver.ConstrainSubtypeRelation(other.NormalizeExpand(), proxy, errorMsg, true);
                  convertedIntoOtherTypeConstraints = true;
                  return true;
                } else if (fullstrength) {
                  // the following is rather aggressive
                  if (Resolver.TypeConstraintsIncludeProxy(other, proxy)) {
                    return false;
                  } else {
                    if (other.IsRefType && resolver.HasApplicableNullableRefTypeConstraint_SubDirection(proxy)) {
                      other = other.NormalizeExpand();  // shave off all constraints
                    }
                    satisfied = resolver.AssignProxyAndHandleItsConstraints(proxy, other, true);
                    convertedIntoOtherTypeConstraints = true;
                    break;
                  }
                } else {
                  return false;  // not enough information
                }
              }
              Type a, b;
              satisfied = Type.FromSameHead_Subtype(t, u, out a, out b);
              if (satisfied) {
                Contract.Assert(a.TypeArgs.Count == b.TypeArgs.Count);
                var cl = a is UserDefinedType ? ((UserDefinedType)a).ResolvedClass : null;
                for (int i = 0; i < a.TypeArgs.Count; i++) {
                  resolver.AllXConstraints.Add(new XConstraint_EquatableArg(tok,
                    a.TypeArgs[i], b.TypeArgs[i],
                    a is CollectionType || (cl != null && cl.TypeArgs[i].Variance != TypeParameter.TPVariance.Non),
                    a.IsRefType,
                    errorMsg));
                  moreXConstraints = true;
                }
              }
              break;
            }
          case "EquatableArg": {
              t = Types[0].NormalizeExpandKeepConstraints();
              var u = Types[1].NormalizeExpandKeepConstraints();
              var moreExactThis = (XConstraint_EquatableArg)this;
              if (t is TypeProxy && u is TypeProxy) {
                return false;  // not enough information to do anything sensible
              } else if (t is TypeProxy || u is TypeProxy) {
                TypeProxy proxy;
                Type other;
                if (t is TypeProxy) {
                  proxy = (TypeProxy)t;
                  other = u;
                } else {
                  proxy = (TypeProxy)u;
                  other = t;
                }
                if (other.IsNumericBased() || other.IsBitVectorType || other.IsBigOrdinalType) {
                  resolver.ConstrainSubtypeRelation(other.NormalizeExpand(), proxy, errorMsg, true);
                  convertedIntoOtherTypeConstraints = true;
                  return true;
                } else if (fullstrength) {
                  // the following is rather aggressive
                  if (Resolver.TypeConstraintsIncludeProxy(other, proxy)) {
                    return false;
                  } else {
                    if (other.IsRefType && resolver.HasApplicableNullableRefTypeConstraint_SubDirection(proxy)) {
                      other = other.NormalizeExpand();  // shave off all constraints
                    }
                    satisfied = resolver.AssignProxyAndHandleItsConstraints(proxy, other, true);
                    convertedIntoOtherTypeConstraints = true;
                    break;
                  }
                } else {
                  return false;  // not enough information
                }
              }
              if (moreExactThis.TreatTypeParamAsWild && (t.IsTypeParameter || u.IsTypeParameter || t.IsOpaqueType || u.IsOpaqueType)) {
                return true;
              } else if (!moreExactThis.AllowSuperSub) {
                resolver.ConstrainSubtypeRelation_Equal(t, u, errorMsg);
                convertedIntoOtherTypeConstraints = true;
                return true;
              }
              Type a, b;
              // okay if t<:u or u<:t (this makes type inference more manageable, though it is more liberal than one might wish)
              satisfied = Type.FromSameHead_Subtype(t, u, out a, out b);
              if (satisfied) {
                Contract.Assert(a.TypeArgs.Count == b.TypeArgs.Count);
                var cl = a is UserDefinedType ? ((UserDefinedType)a).ResolvedClass : null;
                for (int i = 0; i < a.TypeArgs.Count; i++) {
                  resolver.AllXConstraints.Add(new XConstraint_EquatableArg(tok,
                    a.TypeArgs[i], b.TypeArgs[i],
                    a is CollectionType || (cl != null && cl.TypeArgs[i].Variance != TypeParameter.TPVariance.Non),
                    false,
                    errorMsg));
                  moreXConstraints = true;
                }
              }
              break;
            }
          case "Freshable": {
              var collType = t.AsCollectionType;
              if (collType is SetType || collType is SeqType) {
                t = collType.Arg.NormalizeExpand();
              }
              if (t is TypeProxy) {
                return false;  // there is not enough information
              }
              satisfied = t.IsRefType;
              break;
            }
          case "ModifiesFrame": {
              var u = Types[1].NormalizeExpand();  // eventual ref type
              var collType = t is MapType ? null : t.AsCollectionType;
              if (collType != null) {
                t = collType.Arg.NormalizeExpand();
              }
              if (t is TypeProxy) {
                if (collType != null) {
                  // we know enough to convert into a subtyping constraint
                  resolver.AddXConstraint(Token.NoToken/*bogus, but it seems this token would be used only when integers are involved*/, "IsRefType", t, errorMsg);
                  moreXConstraints = true;
                  resolver.ConstrainSubtypeRelation_Equal(u, t, errorMsg);
                  moreXConstraints = true;
                  convertedIntoOtherTypeConstraints = true;
                  return true;
                } else {
                  return false;  // there is not enough information
                }
              }
              if (t.IsRefType) {
                resolver.ConstrainSubtypeRelation_Equal(u, t, errorMsg);
                convertedIntoOtherTypeConstraints = true;
                return true;
              }
              satisfied = false;
              break;
            }
          case "ReadsFrame": {
              var u = Types[1].NormalizeExpand();  // eventual ref type
              var arrTy = t.AsArrowType;
              if (arrTy != null) {
                t = arrTy.Result.NormalizeExpand();
              }
              var collType = t is MapType ? null : t.AsCollectionType;
              if (collType != null) {
                t = collType.Arg.NormalizeExpand();
              }
              if (t is TypeProxy) {
                if (collType != null) {
                  // we know enough to convert into a subtyping constraint
                  resolver.AddXConstraint(Token.NoToken/*bogus, but it seems this token would be used only when integers are involved*/, "IsRefType", t, errorMsg);
                  resolver.ConstrainSubtypeRelation_Equal(u, t, errorMsg);
                  moreXConstraints = true;
                  convertedIntoOtherTypeConstraints = true;
                  return true;
                } else {
                  return false;  // there is not enough information
                }
              }
              if (t.IsRefType && (arrTy == null || collType != null)) {
                resolver.ConstrainSubtypeRelation_Equal(u, t, errorMsg);
                convertedIntoOtherTypeConstraints = true;
                return true;
              }
              satisfied = false;
              break;
            }
          default:
            Contract.Assume(false);  // unknown XConstraint
            return false;  // to please the compiler
        }
        if (!satisfied) {
          errorMsg.FlagAsError(resolver);
        }
        return true;  // the XConstraint has served its purpose
      }

      public bool ProxyWithNoSubTypeConstraint(Type u, Resolver resolver) {
        Contract.Requires(u != null);
        Contract.Requires(resolver != null);
        var proxy = u as TypeProxy;
        if (proxy != null) {
          if (proxy.SubtypeConstraints.Any()) {
            return false;
          }
          foreach (var xc in resolver.AllXConstraints) {
            if (xc.ConstraintName == "Assignable" && xc.Types[0] == proxy) {
              return false;
            }
          }
          return true;
        }
        return false;
      }

      internal bool CouldBeAnything() {
        return Types.All(t => t.NormalizeExpand() is TypeProxy);
      }

      /// <summary>
      /// If "t" or any type among its transitive sub/super-types (depending on "towardsSub")
      /// is a collection type, then returns the element/domain type of that collection.
      /// Otherwise, returns null.
      /// </summary>
      static Type FindCollectionType(Type t, bool towardsSub, ISet<TypeProxy> visited) {
        Contract.Requires(t != null);
        Contract.Requires(visited != null);
        t = t.NormalizeExpand();
        if (DafnyOptions.O.TypeInferenceDebug) {
          Console.WriteLine("DEBUG: FindCollectionType({0}, {1})", t, towardsSub ? "sub" : "super");
        }
        if (t is CollectionType) {
          if (DafnyOptions.O.TypeInferenceDebug) {
            Console.WriteLine("DEBUG: FindCollectionType({0}) = {1}", t, ((CollectionType)t).Arg);
          }
          return ((CollectionType)t).Arg;
        }
        var proxy = t as TypeProxy;
        if (proxy == null || visited.Contains(proxy)) {
          return null;
        }
        visited.Add(proxy);
        foreach (var sub in towardsSub ? proxy.Subtypes : proxy.Supertypes) {
          var e = FindCollectionType(sub, towardsSub, visited);
          if (e != null) {
            return e;
          }
        }
        return null;
      }
    }

    public class XConstraintWithExprs : XConstraint {
      public readonly Expression[] Exprs;
      public XConstraintWithExprs(IToken tok, string constraintName, Type[] types, Expression[] exprs, TypeConstraint.ErrorMsg errMsg)
        : base(tok, constraintName, types, errMsg) {
        Contract.Requires(tok != null);
        Contract.Requires(constraintName != null);
        Contract.Requires(types != null);
        Contract.Requires(exprs != null);
        Contract.Requires(errMsg != null);
        this.Exprs = exprs;
      }
    }

    public class XConstraint_EquatableArg : XConstraint {
      public bool AllowSuperSub;
      public bool TreatTypeParamAsWild;
      public XConstraint_EquatableArg(IToken tok, Type a, Type b, bool allowSuperSub, bool treatTypeParamAsWild, TypeConstraint.ErrorMsg errMsg)
        : base(tok, "EquatableArg", new Type[] { a, b }, errMsg) {
        Contract.Requires(tok != null);
        Contract.Requires(a != null);
        Contract.Requires(b != null);
        Contract.Requires(errMsg != null);
        AllowSuperSub = allowSuperSub;
        TreatTypeParamAsWild = treatTypeParamAsWild;
      }
    }

    /// <summary>
    /// Solves or simplifies as many type constraints as possible.
    /// If "allowDecisions" is "false", then no decisions, only determined inferences, are made; this mode is
    /// appropriate for the partial solving that's done before a member lookup.
    /// </summary>
    public void PartiallySolveTypeConstraints(bool allowDecisions) {
      int state = 0;
      while (true) {
        if (2 <= state && !allowDecisions) {
          // time to say goodnight to Napoli
          return;
        } else if (AllTypeConstraints.Count == 0 && AllXConstraints.Count == 0) {
          // we're done
          return;
        }

        var anyNewConstraints = false;
        var fullStrength = false;
        // Process subtyping constraints
        PrintTypeConstraintState(220 + 2 * state);
        switch (state) {
          case 0: {
              var allTypeConstraints = AllTypeConstraints;
              AllTypeConstraints = new List<TypeConstraint>();
              var processed = new HashSet<TypeConstraint>();
              foreach (var c in allTypeConstraints) {
                ProcessOneSubtypingConstraintAndItsSubs(c, processed, fullStrength, ref anyNewConstraints);
              }

              allTypeConstraints = new List<TypeConstraint>(AllTypeConstraints);  // copy the list
              foreach (var c in allTypeConstraints) {
                var super = c.Super.NormalizeExpand() as TypeProxy;
                if (AssignKnownEnd(super, true, fullStrength)) {
                  anyNewConstraints = true;
                } else if (super != null && fullStrength && AssignKnownEndsFullstrength(super)) {  // KRML: is this used any more?
                  anyNewConstraints = true;
                }
              }
            }
            break;

          case 1: {
              // Process XConstraints
              // confirm as many XConstraints as possible, setting "anyNewConstraints" to "true" if the confirmation
              // of an XConstraint gives rise to new constraints to be handled in the loop above
              bool generatedMoreXConstraints;
              do {
                generatedMoreXConstraints = false;
                var allXConstraints = AllXConstraints;
                AllXConstraints = new List<XConstraint>();
                foreach (var xc in allXConstraints) {
                  bool convertedIntoOtherTypeConstraints, moreXConstraints;
                  if (xc.Confirm(this, fullStrength, out convertedIntoOtherTypeConstraints, out moreXConstraints)) {
                    if (convertedIntoOtherTypeConstraints) {
                      anyNewConstraints = true;
                    } else {
                      generatedMoreXConstraints = true;
                    }
                    if (moreXConstraints) {
                      generatedMoreXConstraints = true;
                    }
                  } else {
                    AllXConstraints.Add(xc);
                  }
                }
              } while (generatedMoreXConstraints);
            }
            break;

          case 2: {
              var assignables = AllXConstraints.Where(xc => xc.ConstraintName == "Assignable").ToList();
              var postponeForNow = new HashSet<TypeProxy>();
              foreach (var constraint in AllTypeConstraints) {
                var lhs = constraint.Super.NormalizeExpandKeepConstraints() as NonProxyType;
                if (lhs != null) {
                  foreach (var ta in lhs.TypeArgs) {
                    AddAllProxies(ta, postponeForNow);
                  }
                }
              }
              foreach (var constraint in AllTypeConstraints) {
                var lhs = constraint.Super.Normalize() as TypeProxy;
                if (lhs != null && !postponeForNow.Contains(lhs)) {
                  var rhss = assignables.Where(xc => xc.Types[0].Normalize() == lhs).Select(xc => xc.Types[1]).ToList();
                  if (ProcessAssignable(lhs, rhss)) {
                    anyNewConstraints = true;  // next time around the big loop, start with state 0 again
                  }
                }
              }
              foreach (var assignable in assignables) {
                var lhs = assignable.Types[0].Normalize() as TypeProxy;
                if (lhs != null && !postponeForNow.Contains(lhs)) {
                  var rhss = assignables.Where(xc => xc.Types[0].Normalize() == lhs).Select(xc => xc.Types[1]).ToList();
                  if (ProcessAssignable(lhs, rhss)) {
                    anyNewConstraints = true;  // next time around the big loop, start with state 0 again
                                               // process only one Assignable constraint in this way
                    break;
                  }
                }
              }
            }
            break;

          case 3:
            anyNewConstraints = ConvertAssignableToSubtypeConstraints(null);
            break;

          case 4: {
              var allTC = AllTypeConstraints;
              AllTypeConstraints = new List<TypeConstraint>();
              var proxyProcessed = new HashSet<TypeProxy>();
              foreach (var c in allTC) {
                ProcessFullStrength_SubDirection(c.Super, proxyProcessed, ref anyNewConstraints);
              }
              foreach (var xc in AllXConstraints) {
                if (xc.ConstraintName == "Assignable") {
                  ProcessFullStrength_SubDirection(xc.Types[0], proxyProcessed, ref anyNewConstraints);
                }
              }
              if (!anyNewConstraints) {
                // only do super-direction if sub-direction had no effect
                proxyProcessed = new HashSet<TypeProxy>();
                foreach (var c in allTC) {
                  ProcessFullStrength_SuperDirection(c.Sub, proxyProcessed, ref anyNewConstraints);
                }
                foreach (var xc in AllXConstraints) {
                  if (xc.ConstraintName == "Assignable") {
                    ProcessFullStrength_SuperDirection(xc.Types[1], proxyProcessed, ref anyNewConstraints);
                  }
                }
              }
              AllTypeConstraints.AddRange(allTC);
            }
            break;

          case 5: {
              // Process default numeric types
              var allTypeConstraints = AllTypeConstraints;
              AllTypeConstraints = new List<TypeConstraint>();
              foreach (var c in allTypeConstraints) {
                if (c.Super is ArtificialType) {
                  var proxy = c.Sub.NormalizeExpand() as TypeProxy;
                  if (proxy != null) {
                    AssignProxyAndHandleItsConstraints(proxy, c.Super is IntVarietiesSupertype ? (Type)Type.Int : Type.Real);
                    anyNewConstraints = true;
                    continue;
                  }
                }
                AllTypeConstraints.Add(c);
              }
            }
            break;

          case 6: {
              fullStrength = true;
              bool generatedMoreXConstraints;
              do {
                generatedMoreXConstraints = false;
                var allXConstraints = AllXConstraints;
                AllXConstraints = new List<XConstraint>();
                foreach (var xc in allXConstraints) {
                  bool convertedIntoOtherTypeConstraints, moreXConstraints;
                  if ((xc.ConstraintName == "Equatable" || xc.ConstraintName == "EquatableArg") && xc.Confirm(this, fullStrength, out convertedIntoOtherTypeConstraints, out moreXConstraints)) {
                    if (convertedIntoOtherTypeConstraints) {
                      anyNewConstraints = true;
                    } else {
                      generatedMoreXConstraints = true;
                    }
                    if (moreXConstraints) {
                      generatedMoreXConstraints = true;
                    }
                  } else {
                    AllXConstraints.Add(xc);
                  }
                }
              } while (generatedMoreXConstraints);
            }
            break;

          case 7: {
              // Process default reference types
              var allXConstraints = AllXConstraints;
              AllXConstraints = new List<XConstraint>();
              foreach (var xc in allXConstraints) {
                if (xc.ConstraintName == "IsRefType" || xc.ConstraintName == "IsNullableRefType") {
                  var proxy = xc.Types[0].Normalize() as TypeProxy;  // before we started processing default types, this would have been a proxy (since it's still in the A
                  if (proxy != null) {
                    AssignProxyAndHandleItsConstraints(proxy, builtIns.ObjectQ());
                    anyNewConstraints = true;
                    continue;
                  }
                }
                AllXConstraints.Add(xc);
              }
            }
            break;

          case 8: fullStrength = true; goto case 0;
          case 9: fullStrength = true; goto case 1;

          case 10: {
              // Finally, collapse constraints involving only proxies, which will have the effect of trading some type error
              // messages for type-underspecification messages.
              var allTypeConstraints = AllTypeConstraints;
              AllTypeConstraints = new List<TypeConstraint>();
              foreach (var c in allTypeConstraints) {
                var super = c.Super.NormalizeExpand();
                var sub = c.Sub.NormalizeExpand();
                if (super == sub) {
                  continue;
                } else if (super is TypeProxy && sub is TypeProxy) {
                  var proxy = (TypeProxy)super;
                  if (DafnyOptions.O.TypeInferenceDebug) {
                    Console.WriteLine("DEBUG: (merge in PartiallySolve) assigning proxy {0}.T := {1}", proxy, sub);
                  }
                  proxy.T = sub;
                  anyNewConstraints = true;  // signal a change in the constraints
                  continue;
                }
                AllTypeConstraints.Add(c);
              }
            }
            break;

          case 11: {
              // Last resort decisions. Sometimes get here even with some 'obvious'
              // inferences. Before this case was added, the type inference returned with
              // failure, so this is a conservative addition, and could be made more
              // capable.
              if (!allowDecisions) {
                break;
              }

              foreach (var c in AllXConstraints) {
                if (c.ConstraintName == "EquatableArg") {
                  ConstrainSubtypeRelation_Equal(c.Types[0], c.Types[1], c.errorMsg);
                  anyNewConstraints = true;
                  AllXConstraints.Remove(c);
                  break;
                }
              }
              if (anyNewConstraints) {
                break;
              }

              TypeConstraint.ErrorMsg oneSuperErrorMsg = null;
              TypeConstraint.ErrorMsg oneSubErrorMsg = null;
              var ss = new HashSet<Type>();
              foreach (var c in AllTypeConstraints) {
                var super = c.Super.NormalizeExpand();
                var sub = c.Sub.NormalizeExpand();
                if (super is TypeProxy && !ss.Contains(super)) {
                  ss.Add(super);
                }
                if (sub is TypeProxy && !ss.Contains(sub)) {
                  ss.Add(sub);
                }
              }

              foreach (var t in ss) {
                var lowers = new HashSet<Type>();
                var uppers = new HashSet<Type>();
                foreach (var c in AllTypeConstraints) {
                  var super = c.Super.NormalizeExpand();
                  var sub = c.Sub.NormalizeExpand();
                  if (t.Equals(super)) {
                    lowers.Add(sub);
                    oneSubErrorMsg = c.ErrMsg;
                  }
                  if (t.Equals(sub)) {
                    uppers.Add(super);
                    oneSuperErrorMsg = c.ErrMsg;
                  }
                }

                bool done = false;
                foreach (var tl in lowers) {
                  foreach (var tu in uppers) {
                    if (tl.Equals(tu)) {
                      if (!ContainsAsTypeParameter(tu, t)) {
                        var errorMsg = new TypeConstraint.ErrorMsgWithBase(AllTypeConstraints[0].ErrMsg,
                          "Decision: {0} is decided to be {1} because the latter is both the upper and lower bound to the proxy",
                          t, tu);
                        ConstrainSubtypeRelation_Equal(t, tu, errorMsg);
                        // The above changes t so that it is a proxy with an assigned type
                        anyNewConstraints = true;
                        done = true;
                        break;
                      }
                    }
                  }
                  if (done) {
                    break;
                  }
                }
              }
              if (anyNewConstraints) {
                break;
              }

              foreach (var t in ss) {
                var lowers = new HashSet<Type>();
                var uppers = new HashSet<Type>();
                foreach (var c in AllTypeConstraints) {
                  var super = c.Super.NormalizeExpand();
                  var sub = c.Sub.NormalizeExpand();
                  if (t.Equals(super)) {
                    lowers.Add(sub);
                  }

                  if (t.Equals(sub)) {
                    uppers.Add(super);
                  }
                }

                if (uppers.Count == 0) {
                  if (lowers.Count == 1) {
                    var em = lowers.GetEnumerator();
                    em.MoveNext();
                    if (!ContainsAsTypeParameter(em.Current, t)) {
                      var errorMsg = new TypeConstraint.ErrorMsgWithBase(oneSubErrorMsg,
                        "Decision: {0} is decided to be {1} because the latter is a lower bound to the proxy and there is no constraint with an upper bound",
                        t, em.Current);
                      ConstrainSubtypeRelation_Equal(t, em.Current, errorMsg);
                      anyNewConstraints = true;
                      break;
                    }
                  }
                }
                if (lowers.Count == 0) {
                  if (uppers.Count == 1) {
                    var em = uppers.GetEnumerator();
                    em.MoveNext();
                    if (!ContainsAsTypeParameter(em.Current, t)) {
                      var errorMsg = new TypeConstraint.ErrorMsgWithBase(oneSuperErrorMsg,
                        "Decision: {0} is decided to be {1} because the latter is an upper bound to the proxy and there is no constraint with a lower bound",
                        t, em.Current);
                      ConstrainSubtypeRelation_Equal(t, em.Current, errorMsg);
                      anyNewConstraints = true;
                      break;
                    }
                  }
                }
              }

              break;
            }

          case 12:
            // we're so out of here
            return;
        }
        if (anyNewConstraints) {
          state = 0;
        } else {
          state++;
        }
      }
    }

    TypeProxy NewIntegerBasedProxy(IToken tok) {
      Contract.Requires(tok != null);
      var proxy = new InferredTypeProxy();
      ConstrainSubtypeRelation(new IntVarietiesSupertype(), proxy, tok, "integer literal used as if it had type {0}", proxy);
      return proxy;
    }

    private bool ContainsAsTypeParameter(Type t, Type u) {
      if (t.Equals(u)) {
        return true;
      }

      if (t is UserDefinedType udt) {
        foreach (var tp in udt.TypeArgs) {
          if (ContainsAsTypeParameter(tp, u)) {
            return true;
          }
        }
      }
      if (t is CollectionType st) {
        foreach (var tp in st.TypeArgs) {
          if (ContainsAsTypeParameter(tp, u)) {
            return true;
          }
        }
      }
      return false;
    }

    private void AddAllProxies(Type type, HashSet<TypeProxy> proxies) {
      Contract.Requires(type != null);
      Contract.Requires(proxies != null);
      var proxy = type as TypeProxy;
      if (proxy != null) {
        proxies.Add(proxy);
      } else {
        foreach (var ta in type.TypeArgs) {
          AddAllProxies(ta, proxies);
        }
      }
    }

    /// <summary>
    /// Set "lhs" to the join of "rhss" and "lhs.Subtypes, if possible.
    /// Returns "true' if something was done, or "false" otherwise.
    /// </summary>
    private bool ProcessAssignable(TypeProxy lhs, List<Type> rhss) {
      Contract.Requires(lhs != null && lhs.T == null);
      Contract.Requires(rhss != null);
      if (DafnyOptions.O.TypeInferenceDebug) {
        Console.Write("DEBUG: ProcessAssignable: {0} with rhss:", lhs);
        foreach (var rhs in rhss) {
          Console.Write(" {0}", rhs);
        }
        Console.Write(" subtypes:");
        foreach (var sub in lhs.SubtypesKeepConstraints) {
          Console.Write(" {0}", sub);
        }
        Console.WriteLine();
      }
      Type join = null;
      foreach (var rhs in rhss) {
        if (rhs is TypeProxy) { return false; }
        join = join == null ? rhs : Type.Join(join, rhs, builtIns);
      }
      foreach (var sub in lhs.SubtypesKeepConstraints) {
        if (sub is TypeProxy) { return false; }
        join = join == null ? sub : Type.Join(join, sub, builtIns);
      }
      if (join == null) {
        return false;
      } else if (Reaches(join, lhs, 1, new HashSet<TypeProxy>())) {
        // would cause a cycle, so don't do it
        return false;
      } else {
        if (DafnyOptions.O.TypeInferenceDebug) {
          Console.WriteLine("DEBUG: ProcessAssignable: assigning proxy {0}.T := {1}", lhs, join);
        }
        lhs.T = join;
        return true;
      }
    }

    /// <summary>
    /// Convert each Assignable(A, B) constraint into a subtyping constraint A :> B,
    /// provided that:
    ///  - B is a non-proxy, and
    ///  - either "proxySpecialization" is null or some proxy in "proxySpecializations" prominently appears in A.
    /// </summary>
    bool ConvertAssignableToSubtypeConstraints(ISet<TypeProxy>/*?*/ proxySpecializations) {
      var anyNewConstraints = false;
      // If (the head of) the RHS of an Assignable is known, convert the XConstraint into a subtyping constraint
      var allX = AllXConstraints;
      AllXConstraints = new List<XConstraint>();
      foreach (var xc in allX) {
        if (xc.ConstraintName == "Assignable" && xc.Types[1].Normalize() is NonProxyType) {
          var t0 = xc.Types[0].NormalizeExpand();
          if (proxySpecializations == null
            || proxySpecializations.Contains(t0)
            || t0.TypeArgs.Exists(ta => proxySpecializations.Contains(ta))) {
            ConstrainSubtypeRelation(t0, xc.Types[1], xc.errorMsg, true);
            anyNewConstraints = true;
            continue;
          }
        }
        AllXConstraints.Add(xc);
      }
      return anyNewConstraints;
    }

    bool TightenUpEquatable(ISet<TypeProxy> proxiesOfInterest) {
      Contract.Requires(proxiesOfInterest != null);
      var anyNewConstraints = false;
      var allX = AllXConstraints;
      AllXConstraints = new List<XConstraint>();
      foreach (var xc in allX) {
        if (xc.ConstraintName == "Equatable" || xc.ConstraintName == "EquatableArg") {
          var t0 = xc.Types[0].NormalizeExpandKeepConstraints();
          var t1 = xc.Types[1].NormalizeExpandKeepConstraints();
          if (proxiesOfInterest.Contains(t0) || proxiesOfInterest.Contains(t1)) {
            ConstrainSubtypeRelation_Equal(t0, t1, xc.errorMsg);
            anyNewConstraints = true;
            continue;
          }
        }
        AllXConstraints.Add(xc);
      }
      return anyNewConstraints;
    }

    void ProcessOneSubtypingConstraintAndItsSubs(TypeConstraint c, ISet<TypeConstraint> processed, bool fullStrength, ref bool anyNewConstraints) {
      Contract.Requires(c != null);
      Contract.Requires(processed != null);
      if (processed.Contains(c)) {
        return;  // our job has already been done, or is at least in progress
      }
      processed.Add(c);

      var super = c.Super.NormalizeExpandKeepConstraints();
      var sub = c.Sub.NormalizeExpandKeepConstraints();
      // Process all subtype types before going on
      var subProxy = sub as TypeProxy;
      if (subProxy != null) {
        foreach (var cc in subProxy.SubtypeConstraints) {
          ProcessOneSubtypingConstraintAndItsSubs(cc, processed, fullStrength, ref anyNewConstraints);
        }
      }
      // the processing may have assigned some proxies, so we'll refresh super and sub
      super = super.NormalizeExpandKeepConstraints();
      sub = sub.NormalizeExpandKeepConstraints();

      if (super.Equals(sub)) {
        // the constraint is satisfied, so just drop it
      } else if ((super is NonProxyType || super is ArtificialType) && sub is NonProxyType) {
        ImposeSubtypingConstraint(super, sub, c.ErrMsg);
        anyNewConstraints = true;
      } else if (AssignKnownEnd(sub as TypeProxy, true, fullStrength)) {
        anyNewConstraints = true;
      } else if (sub is TypeProxy && fullStrength && AssignKnownEndsFullstrength((TypeProxy)sub)) {
        anyNewConstraints = true;
      } else {
        // keep the constraint for now
        AllTypeConstraints.Add(c);
      }
    }

    void ProcessFullStrength_SubDirection(Type t, ISet<TypeProxy> processed, ref bool anyNewConstraints) {
      Contract.Requires(t != null);
      Contract.Requires(processed != null);
      var proxy = t.NormalizeExpand() as TypeProxy;
      if (proxy != null) {
        if (processed.Contains(proxy)) {
          return;  // our job has already been done, or is at least in progress
        }
        processed.Add(proxy);

        foreach (var u in proxy.SubtypesKeepConstraints_WithAssignable(AllXConstraints)) {
          ProcessFullStrength_SubDirection(u, processed, ref anyNewConstraints);
        }
        proxy = proxy.NormalizeExpand() as TypeProxy;
        if (proxy != null && AssignKnownEndsFullstrength_SubDirection(proxy)) {
          anyNewConstraints = true;
        }
      }
    }

    void ProcessFullStrength_SuperDirection(Type t, ISet<TypeProxy> processed, ref bool anyNewConstraints) {
      Contract.Requires(t != null);
      Contract.Requires(processed != null);
      var proxy = t.NormalizeExpand() as TypeProxy;
      if (proxy != null) {
        if (processed.Contains(proxy)) {
          return;  // our job has already been done, or is at least in progress
        }
        processed.Add(proxy);

        foreach (var u in proxy.Supertypes) {
          ProcessFullStrength_SuperDirection(u, processed, ref anyNewConstraints);
        }
        proxy = proxy.NormalizeExpand() as TypeProxy;
        if (proxy != null && AssignKnownEndsFullstrength_SuperDirection(proxy)) {
          anyNewConstraints = true;
        }
      }
    }

    /// <summary>
    /// Returns true if anything happened.
    /// </summary>
    bool AssignKnownEnd(TypeProxy proxy, bool keepConstraints, bool fullStrength) {
      Contract.Requires(proxy == null || proxy.T == null);  // caller is supposed to have called NormalizeExpand
      if (proxy == null) {
        // nothing to do
        return false;
      }
      // ----- first, go light; also, prefer subtypes over supertypes
      IEnumerable<Type> subTypes = keepConstraints ? proxy.SubtypesKeepConstraints : proxy.Subtypes;
      foreach (var su in subTypes) {
        DetermineRootLeaf(su, out var isRoot, out _, out var headRoot, out _);
        Contract.Assert(!isRoot || headRoot);  // isRoot ==> headRoot
        if (isRoot) {
          if (Reaches(su, proxy, 1, new HashSet<TypeProxy>())) {
            // adding a constraint here would cause a bad cycle, so we don't
          } else {
            AssignProxyAndHandleItsConstraints(proxy, su, keepConstraints);
            return true;
          }
        } else if (headRoot) {
          if (Reaches(su, proxy, 1, new HashSet<TypeProxy>())) {
            // adding a constraint here would cause a bad cycle, so we don't
          } else {
            AssignProxyAndHandleItsConstraints(proxy, TypeProxy.HeadWithProxyArgs(su), keepConstraints);
            return true;
          }
        }
      }
      if (fullStrength) {
        IEnumerable<Type> superTypes = keepConstraints ? proxy.SupertypesKeepConstraints : proxy.Supertypes;
        foreach (var su in superTypes) {
          DetermineRootLeaf(su, out _, out var isLeaf, out _, out var headLeaf);
          Contract.Assert(!isLeaf || headLeaf);  // isLeaf ==> headLeaf
          if (isLeaf) {
            if (Reaches(su, proxy, -1, new HashSet<TypeProxy>())) {
              // adding a constraint here would cause a bad cycle, so we don't
            } else {
              AssignProxyAndHandleItsConstraints(proxy, su, keepConstraints);
              return true;
            }
          } else if (headLeaf) {
            if (Reaches(su, proxy, -1, new HashSet<TypeProxy>())) {
              // adding a constraint here would cause a bad cycle, so we don't
            } else {
              AssignProxyAndHandleItsConstraints(proxy, TypeProxy.HeadWithProxyArgs(su), keepConstraints);
              return true;
            }
          }
        }
      }
      return false;
    }

    bool AssignKnownEndsFullstrength(TypeProxy proxy) {
      Contract.Requires(proxy != null);
      // ----- continue with full strength
      // If the join of the subtypes exists, use it
      var joins = new List<Type>();
      foreach (var su in proxy.Subtypes) {
        if (su is TypeProxy) {
          continue;  // don't include proxies in the meet computation
        }
        int i = 0;
        for (; i < joins.Count; i++) {
          var j = Type.Join(joins[i], su, builtIns);
          if (j != null) {
            joins[i] = j;
            break;
          }
        }
        if (i == joins.Count) {
          // we went to the end without finding a place to meet up
          joins.Add(su);
        }
      }
      if (joins.Count == 1 && !Reaches(joins[0], proxy, 1, new HashSet<TypeProxy>())) {
        // we were able to compute a meet of all the subtyping constraints, so use it
        AssignProxyAndHandleItsConstraints(proxy, joins[0]);
        return true;
      }
      // If the meet of the supertypes exists, use it
      var meets = new List<Type>();
      foreach (var su in proxy.Supertypes) {
        if (su is TypeProxy) {
          continue;  // don't include proxies in the meet computation
        }
        int i = 0;
        for (; i < meets.Count; i++) {
          var j = Type.Meet(meets[i], su, builtIns);
          if (j != null) {
            meets[i] = j;
            break;
          }
        }
        if (i == meets.Count) {
          // we went to the end without finding a place to meet
          meets.Add(su);
        }
      }
      if (meets.Count == 1 && !(meets[0] is ArtificialType) && !Reaches(meets[0], proxy, -1, new HashSet<TypeProxy>())) {
        // we were able to compute a meet of all the subtyping constraints, so use it
        AssignProxyAndHandleItsConstraints(proxy, meets[0]);
        return true;
      }

      return false;
    }

    bool AssignKnownEndsFullstrength_SubDirection(TypeProxy proxy) {
      Contract.Requires(proxy != null && proxy.T == null);
      // If the join the subtypes exists, use it
      var joins = new List<Type>();
      var proxySubs = new HashSet<TypeProxy>();
      proxySubs.Add(proxy);
      foreach (var su in proxy.SubtypesKeepConstraints_WithAssignable(AllXConstraints)) {
        if (su is TypeProxy) {
          proxySubs.Add((TypeProxy)su);
        } else {
          int i = 0;
          for (; i < joins.Count; i++) {
            var j = Type.Join(joins[i], su, builtIns);
            if (j != null) {
              joins[i] = j;
              break;
            }
          }
          if (i == joins.Count) {
            // we went to the end without finding a place to join in
            joins.Add(su);
          }
        }
      }
      if (joins.Count == 1 && !Reaches(joins[0], proxy, 1, new HashSet<TypeProxy>())) {
        // We were able to compute a join of all the subtyping constraints, so use it.
        // Well, maybe.  If "join[0]" denotes a non-null type and "proxy" is something
        // that could be assigned "null", then set "proxy" to the nullable version of "join[0]".
        // Stated differently, think of an applicable "IsNullableRefType" constraint as
        // being part of the join computation, essentially throwing in a "...?".
        // Except: If the join is a tight bound--meaning, it is also a meet--then pick it
        // after all, because that seems to give rise to less confusing error messages.
        if (joins[0].IsNonNullRefType) {
          Type meet = null;
          if (MeetOfAllSupertypes(proxy, ref meet, new HashSet<TypeProxy>(), false) && meet != null && Type.SameHead(joins[0], meet)) {
            // leave it
          } else {
            CloseOverAssignableRhss(proxySubs);
            if (HasApplicableNullableRefTypeConstraint(proxySubs)) {
              if (DafnyOptions.O.TypeInferenceDebug) {
                Console.WriteLine("DEBUG: Found join {0} for proxy {1}, but weakening it to {2}", joins[0], proxy, joins[0].NormalizeExpand());
              }
              AssignProxyAndHandleItsConstraints(proxy, joins[0].NormalizeExpand(), true);
              return true;
            }
          }
        }
        AssignProxyAndHandleItsConstraints(proxy, joins[0], true);
        return true;
      }
      return false;
    }

    private void CloseOverAssignableRhss(ISet<TypeProxy> proxySet) {
      Contract.Requires(proxySet != null);
      while (true) {
        var moreChanges = false;
        foreach (var xc in AllXConstraints) {
          if (xc.ConstraintName == "Assignable") {
            var source = xc.Types[0].Normalize() as TypeProxy;
            var sink = xc.Types[1].Normalize() as TypeProxy;
            if (source != null && sink != null && proxySet.Contains(source) && !proxySet.Contains(sink)) {
              proxySet.Add(sink);
              moreChanges = true;
            }
          }
        }
        if (!moreChanges) {
          return;
        }
      }
    }
    private bool HasApplicableNullableRefTypeConstraint(ISet<TypeProxy> proxySet) {
      Contract.Requires(proxySet != null);
      var nullableProxies = new HashSet<TypeProxy>();
      foreach (var xc in AllXConstraints) {
        if (xc.ConstraintName == "IsNullableRefType") {
          var npr = xc.Types[0].Normalize() as TypeProxy;
          if (npr != null) {
            nullableProxies.Add(npr);
          }
        }
      }
      return proxySet.Any(nullableProxies.Contains);
    }
    private bool HasApplicableNullableRefTypeConstraint_SubDirection(TypeProxy proxy) {
      Contract.Requires(proxy != null);
      var nullableProxies = new HashSet<TypeProxy>();
      foreach (var xc in AllXConstraints) {
        if (xc.ConstraintName == "IsNullableRefType") {
          var npr = xc.Types[0].Normalize() as TypeProxy;
          if (npr != null) {
            nullableProxies.Add(npr);
          }
        }
      }
      return HasApplicableNullableRefTypeConstraint_SubDirection_aux(proxy, nullableProxies, new HashSet<TypeProxy>());
    }
    private bool HasApplicableNullableRefTypeConstraint_SubDirection_aux(TypeProxy proxy, ISet<TypeProxy> nullableProxies, ISet<TypeProxy> visitedProxies) {
      Contract.Requires(proxy != null);
      Contract.Requires(nullableProxies != null);
      Contract.Requires(visitedProxies != null);

      if (visitedProxies.Contains(proxy)) {
        return false;
      }
      visitedProxies.Add(proxy);

      if (nullableProxies.Contains(proxy)) {
        return true;
      }

      foreach (var sub in proxy.SubtypesKeepConstraints_WithAssignable(AllXConstraints)) {
        var psub = sub as TypeProxy;
        if (psub != null && HasApplicableNullableRefTypeConstraint_SubDirection_aux(psub, nullableProxies, visitedProxies)) {
          return true;
        }
      }
      return false;
    }

    bool AssignKnownEndsFullstrength_SuperDirection(TypeProxy proxy) {
      Contract.Requires(proxy != null && proxy.T == null);
      // First, compute the the join of the Assignable LHSs.  Then, compute
      // the meet of that join and the supertypes.
      var joins = new List<Type>();
      foreach (var xc in AllXConstraints) {
        if (xc.ConstraintName == "Assignable" && xc.Types[1].Normalize() == proxy) {
          var su = xc.Types[0].Normalize();
          if (su is TypeProxy) {
            continue; // don't include proxies in the join computation
          }
          int i = 0;
          for (; i < joins.Count; i++) {
            var j = Type.Join(joins[i], su, builtIns);
            if (j != null) {
              joins[i] = j;
              break;
            }
          }
          if (i == joins.Count) {
            // we went to the end without finding a place to join in
            joins.Add(su);
          }
        }
      }
      // If the meet of the supertypes exists, use it
      var meets = new List<Type>(joins);
      foreach (var su in proxy.SupertypesKeepConstraints) {
        if (su is TypeProxy) {
          continue;  // don't include proxies in the meet computation
        }
        int i = 0;
        for (; i < meets.Count; i++) {
          var j = Type.Meet(meets[i], su, builtIns);
          if (j != null) {
            meets[i] = j;
            break;
          }
        }
        if (i == meets.Count) {
          // we went to the end without finding a place to meet up
          meets.Add(su);
        }
      }
      if (meets.Count == 1 && !(meets[0] is ArtificialType) && !Reaches(meets[0], proxy, -1, new HashSet<TypeProxy>())) {
        // we were able to compute a meet of all the subtyping constraints, so use it
        AssignProxyAndHandleItsConstraints(proxy, meets[0], true);
        return true;
      }
      return false;
    }

    int _reaches_recursion;
    private bool Reaches(Type t, TypeProxy proxy, int direction, HashSet<TypeProxy> visited) {
      if (_reaches_recursion == 20) {
        Contract.Assume(false);  // possible infinite recursion
      }
      _reaches_recursion++;
      var b = Reaches_aux(t, proxy, direction, visited);
      _reaches_recursion--;
      return b;
    }
    private bool Reaches_aux(Type t, TypeProxy proxy, int direction, HashSet<TypeProxy> visited) {
      Contract.Requires(t != null);
      Contract.Requires(proxy != null);
      Contract.Requires(visited != null);
      t = t.NormalizeExpand();
      var tproxy = t as TypeProxy;
      if (tproxy == null) {
        var polarities = Type.GetPolarities(t).ConvertAll(TypeParameter.Direction);
        Contract.Assert(polarities != null);
        Contract.Assert(polarities.Count <= t.TypeArgs.Count);
        for (int i = 0; i < polarities.Count; i++) {
          if (Reaches(t.TypeArgs[i], proxy, direction * polarities[i], visited)) {
            return true;
          }
        }
        return false;
      } else if (tproxy == proxy) {
        return true;
      } else if (visited.Contains(tproxy)) {
        return false;
      } else {
        visited.Add(tproxy);
        if (0 <= direction && tproxy.Subtypes.Any(su => Reaches(su, proxy, direction, visited))) {
          return true;
        }
        if (direction <= 0 && tproxy.Supertypes.Any(su => Reaches(su, proxy, direction, visited))) {
          return true;
        }
        return false;
      }
    }

    /// <summary>
    /// Assumes type parameters have already been pushed, and that all types in class members have been resolved
    /// </summary>
    void ResolveClassMemberBodiesInitial(TopLevelDeclWithMembers cl) {
      Contract.Requires(cl != null);
      Contract.Requires(currentClass == null);
      Contract.Requires(AllTypeConstraints.Count == 0);
      Contract.Ensures(currentClass == null);
      Contract.Ensures(AllTypeConstraints.Count == 0);

      currentClass = cl;
      foreach (MemberDecl member in cl.Members) {
        Contract.Assert(VisibleInScope(member));
        if (member is ConstantField { Rhs: { } } constantField) {
          var resolutionContext = new ResolutionContext(constantField, false);
          scope.PushMarker();
          if (constantField.IsStatic || currentClass == null || !currentClass.AcceptThis) {
            scope.AllowInstance = false;
          }
          ResolveExpression(constantField.Rhs, resolutionContext);
          scope.PopMarker();
          AddAssignableConstraint(constantField.tok, constantField.Type, constantField.Rhs.Type,
            "type for constant '" + constantField.Name + "' is '{0}', but its initialization value type is '{1}'");
          SolveAllTypeConstraints();
        }
      }
      currentClass = null;
    }

    /// <summary>
    /// Assumes type parameters have already been pushed, and that all types in class members have been resolved
    /// </summary>
    void ResolveClassMemberBodies(TopLevelDeclWithMembers cl) {
      Contract.Requires(cl != null);
      Contract.Requires(currentClass == null);
      Contract.Requires(AllTypeConstraints.Count == 0);
      Contract.Ensures(currentClass == null);
      Contract.Ensures(AllTypeConstraints.Count == 0);

      currentClass = cl;
      foreach (MemberDecl member in cl.Members) {
        Contract.Assert(VisibleInScope(member));
        if (member is Field) {
          var resolutionContext = new ResolutionContext(new NoContext(currentClass.EnclosingModuleDefinition), false);
          scope.PushMarker();
          if (member.IsStatic) {
            scope.AllowInstance = false;
          }
          ResolveAttributes(member, resolutionContext, true);
          scope.PopMarker();

        } else if (member is Function function) {
          var ec = reporter.Count(ErrorLevel.Error);
          allTypeParameters.PushMarker();
          ResolveTypeParameters(function.TypeArgs, false, function);
          function.Resolve(this);
          allTypeParameters.PopMarker();
          if (function is ExtremePredicate { PrefixPredicate: { } prefixPredicate } && ec == reporter.Count(ErrorLevel.Error)) {
            allTypeParameters.PushMarker();
            ResolveTypeParameters(prefixPredicate.TypeArgs, false, prefixPredicate);
            prefixPredicate.Resolve(this);
            allTypeParameters.PopMarker();
          }

        } else if (member is Method method) {
          var ec = reporter.Count(ErrorLevel.Error);
          allTypeParameters.PushMarker();
          ResolveTypeParameters(method.TypeArgs, false, method);
          method.Resolve(this);
          allTypeParameters.PopMarker();
          if (method is ExtremeLemma { PrefixLemma: { } prefixLemma } && ec == reporter.Count(ErrorLevel.Error)) {
            allTypeParameters.PushMarker();
            ResolveTypeParameters(prefixLemma.TypeArgs, false, prefixLemma);
            prefixLemma.Resolve(this);
            allTypeParameters.PopMarker();
          }

        } else {
          Contract.Assert(false); throw new cce.UnreachableException();  // unexpected member type
        }
        Contract.Assert(AllTypeConstraints.Count == 0);
      }
      currentClass = null;
    }

    /// <summary>
    /// Assumes type parameters have already been pushed
    /// </summary>
    void ResolveCtorTypes(DatatypeDecl/*!*/ dt, Graph<IndDatatypeDecl/*!*/>/*!*/ dependencies, Graph<CoDatatypeDecl/*!*/>/*!*/ coDependencies) {
      Contract.Requires(dt != null);
      Contract.Requires(dependencies != null);
      Contract.Requires(coDependencies != null);
      foreach (DatatypeCtor ctor in dt.Ctors) {

        ctor.EnclosingDatatype = dt;

        allTypeParameters.PushMarker();
        ResolveCtorSignature(ctor, dt.TypeArgs);
        allTypeParameters.PopMarker();

        if (dt is IndDatatypeDecl) {
          // The dependencies of interest among inductive datatypes are all (inductive data)types mentioned in the parameter types
          var idt = (IndDatatypeDecl)dt;
          dependencies.AddVertex(idt);
          foreach (Formal p in ctor.Formals) {
            AddDatatypeDependencyEdge(idt, p.Type, dependencies);
          }
        } else {
          // The dependencies of interest among codatatypes are just the top-level types of parameters.
          var codt = (CoDatatypeDecl)dt;
          coDependencies.AddVertex(codt);
          foreach (var p in ctor.Formals) {
            var co = p.Type.AsCoDatatype;
            if (co != null && codt.EnclosingModuleDefinition == co.EnclosingModuleDefinition) {
              coDependencies.AddEdge(codt, co);
            }
          }
        }
      }
    }

    void ResolveCtorSignature(DatatypeCtor ctor, List<TypeParameter> dtTypeArguments) {
      Contract.Requires(ctor != null);
      Contract.Requires(ctor.EnclosingDatatype != null);
      Contract.Requires(dtTypeArguments != null);
      foreach (Formal p in ctor.Formals) {
        ResolveType(p.tok, p.Type, ctor.EnclosingDatatype, ResolveTypeOptionEnum.AllowPrefix, dtTypeArguments);
      }
    }

    void AddDatatypeDependencyEdge(IndDatatypeDecl dt, Type tp, Graph<IndDatatypeDecl> dependencies) {
      Contract.Requires(dt != null);
      Contract.Requires(tp != null);
      Contract.Requires(dependencies != null);  // more expensive check: Contract.Requires(cce.NonNullElements(dependencies));

      tp = tp.NormalizeExpand();
      var dependee = tp.AsIndDatatype;
      if (dependee != null && dt.EnclosingModuleDefinition == dependee.EnclosingModuleDefinition) {
        dependencies.AddEdge(dt, dependee);
        foreach (var ta in ((UserDefinedType)tp).TypeArgs) {
          AddDatatypeDependencyEdge(dt, ta, dependencies);
        }
      }
    }

    public void ResolveFrameExpressionTopLevel(FrameExpression fe, FrameExpressionUse use, ICodeContext codeContext) {
      ResolveFrameExpression(fe, use, new ResolutionContext(codeContext, false));
    }

    void ResolveFrameExpression(FrameExpression fe, FrameExpressionUse use, ResolutionContext resolutionContext) {
      Contract.Requires(fe != null);
      Contract.Requires(resolutionContext != null);

      ResolveExpression(fe.E, resolutionContext);
      Type t = fe.E.Type;
      Contract.Assert(t != null);  // follows from postcondition of ResolveExpression
      var eventualRefType = new InferredTypeProxy();
      if (use == FrameExpressionUse.Reads) {
        AddXConstraint(fe.E.tok, "ReadsFrame", t, eventualRefType,
          "a reads-clause expression must denote an object, a set/iset/multiset/seq of objects, or a function to a set/iset/multiset/seq of objects (instead got {0})");
      } else {
        AddXConstraint(fe.E.tok, "ModifiesFrame", t, eventualRefType,
          use == FrameExpressionUse.Modifies ?
          "a modifies-clause expression must denote an object or a set/iset/multiset/seq of objects (instead got {0})" :
          "an unchanged expression must denote an object or a set/iset/multiset/seq of objects (instead got {0})");
      }
      if (fe.FieldName != null) {
        NonProxyType tentativeReceiverType;
        var member = ResolveMember(fe.E.tok, eventualRefType, fe.FieldName, out tentativeReceiverType);
        var ctype = (UserDefinedType)tentativeReceiverType;  // correctness of cast follows from the DenotesClass test above
        if (member == null) {
          // error has already been reported by ResolveMember
        } else if (!(member is Field)) {
          reporter.Error(MessageSource.Resolver, fe.E, "member {0} in type {1} does not refer to a field", fe.FieldName, ctype.Name);
        } else if (member is ConstantField) {
          reporter.Error(MessageSource.Resolver, fe.E, "expression is not allowed to refer to constant field {0}", fe.FieldName);
        } else {
          Contract.Assert(ctype != null && ctype.ResolvedClass != null);  // follows from postcondition of ResolveMember
          fe.Field = (Field)member;
        }
      }
    }

    /// <summary>
    /// Assumes type parameters have already been pushed
    /// </summary>
    void ResolveIterator(IteratorDecl iter) {
      Contract.Requires(iter != null);
      Contract.Requires(currentClass == null);
      Contract.Ensures(currentClass == null);

      var initialErrorCount = reporter.Count(ErrorLevel.Error);

      // Add in-parameters to the scope, but don't care about any duplication errors, since they have already been reported
      scope.PushMarker();
      scope.AllowInstance = false;  // disallow 'this' from use, which means that the special fields and methods added are not accessible in the syntactically given spec
      iter.Ins.ForEach(p => scope.Push(p.Name, p));
      ResolveParameterDefaultValues(iter.Ins, new ResolutionContext(iter, false));

      // Start resolving specification...
      // we start with the decreases clause, because the _decreases<n> fields were only given type proxies before; we'll know
      // the types only after resolving the decreases clause (and it may be that some of resolution has already seen uses of
      // these fields; so, with no further ado, here we go
      ResolveAttributes(iter.Decreases, new ResolutionContext(iter, false));
      Contract.Assert(iter.Decreases.Expressions.Count == iter.DecreasesFields.Count);
      for (var i = 0; i < iter.Decreases.Expressions.Count; i++) {
        var e = iter.Decreases.Expressions[i];
        ResolveExpression(e, new ResolutionContext(iter, false));
        // any type is fine, but associate this type with the corresponding _decreases<n> field
        var d = iter.DecreasesFields[i];
        // If the following type constraint does not hold, then: Bummer, there was a use--and a bad use--of the field before, so this won't be the best of error messages
        ConstrainSubtypeRelation(d.Type, e.Type, e, "type of field {0} is {1}, but has been constrained elsewhere to be of type {2}", d.Name, e.Type, d.Type);
      }
      foreach (FrameExpression fe in iter.Reads.Expressions) {
        ResolveFrameExpressionTopLevel(fe, FrameExpressionUse.Reads, iter);
      }
      ResolveAttributes(iter.Modifies, new ResolutionContext(iter, false));
      foreach (FrameExpression fe in iter.Modifies.Expressions) {
        ResolveFrameExpressionTopLevel(fe, FrameExpressionUse.Modifies, iter);
      }
      foreach (AttributedExpression e in iter.Requires) {
        ResolveAttributes(e, new ResolutionContext(iter, false));
        ResolveExpression(e.E, new ResolutionContext(iter, false));
        Contract.Assert(e.E.Type != null);  // follows from postcondition of ResolveExpression
        ConstrainTypeExprBool(e.E, "Precondition must be a boolean (got {0})");
      }

      scope.PopMarker();  // for the in-parameters

      // We resolve the rest of the specification in an instance context.  So mentions of the in- or yield-parameters
      // get resolved as field dereferences (with an implicit "this")
      scope.PushMarker();
      currentClass = iter;
      Contract.Assert(scope.AllowInstance);

      foreach (AttributedExpression e in iter.YieldRequires) {
        ResolveAttributes(e, new ResolutionContext(iter, false));
        ResolveExpression(e.E, new ResolutionContext(iter, false));
        Contract.Assert(e.E.Type != null);  // follows from postcondition of ResolveExpression
        ConstrainTypeExprBool(e.E, "Yield precondition must be a boolean (got {0})");
      }
      foreach (AttributedExpression e in iter.YieldEnsures) {
        ResolveAttributes(e, new ResolutionContext(iter, true));
        ResolveExpression(e.E, new ResolutionContext(iter, true));
        Contract.Assert(e.E.Type != null);  // follows from postcondition of ResolveExpression
        ConstrainTypeExprBool(e.E, "Yield postcondition must be a boolean (got {0})");
      }
      foreach (AttributedExpression e in iter.Ensures) {
        ResolveAttributes(e, new ResolutionContext(iter, true));
        ResolveExpression(e.E, new ResolutionContext(iter, true));
        Contract.Assert(e.E.Type != null);  // follows from postcondition of ResolveExpression
        ConstrainTypeExprBool(e.E, "Postcondition must be a boolean (got {0})");
      }
      SolveAllTypeConstraints();

      var postSpecErrorCount = reporter.Count(ErrorLevel.Error);

      // Resolve body
      if (iter.Body != null) {
        DominatingStatementLabels.PushMarker();
        foreach (var req in iter.Requires) {
          if (req.Label != null) {
            if (DominatingStatementLabels.Find(req.Label.Name) != null) {
              reporter.Error(MessageSource.Resolver, req.Label.Tok, "assert label shadows a dominating label");
            } else {
              var rr = DominatingStatementLabels.Push(req.Label.Name, req.Label);
              Contract.Assert(rr == Scope<Label>.PushResult.Success);  // since we just checked for duplicates, we expect the Push to succeed
            }
          }
        }
        ResolveBlockStatement(iter.Body, ResolutionContext.FromCodeContext(iter));
        DominatingStatementLabels.PopMarker();
        SolveAllTypeConstraints();
      }

      currentClass = null;
      scope.PopMarker();  // pop off the AllowInstance setting

      if (postSpecErrorCount == initialErrorCount) {
        iter.CreateIteratorMethodSpecs(this);
      }
    }

    /// <summary>
    /// Checks if lhs, which is expected to be a successfully resolved expression, denotes something
    /// that can be assigned to.  In particular, this means that lhs denotes a mutable variable, field,
    /// or array element.  If a violation is detected, an error is reported.
    /// </summary>
    public void CheckIsLvalue(Expression lhs, ResolutionContext resolutionContext) {
      Contract.Requires(lhs != null);
      Contract.Requires(resolutionContext != null);
      if (lhs is IdentifierExpr) {
        var ll = (IdentifierExpr)lhs;
        if (!ll.Var.IsMutable) {
          reporter.Error(MessageSource.Resolver, lhs, "LHS of assignment must denote a mutable variable");
        }
      } else if (lhs is MemberSelectExpr) {
        var ll = (MemberSelectExpr)lhs;
        var field = ll.Member as Field;
        if (field == null || !field.IsUserMutable) {
          if (resolutionContext.InFirstPhaseConstructor && field is ConstantField cf && !cf.IsStatic && cf.Rhs == null) {
            if (Expression.AsThis(ll.Obj) != null) {
              // it's cool; this field can be assigned to here
            } else {
              reporter.Error(MessageSource.Resolver, lhs, "LHS of assignment must denote a mutable field of 'this'");
            }
          } else {
            reporter.Error(MessageSource.Resolver, lhs, "LHS of assignment must denote a mutable field");
          }
        }
      } else if (lhs is SeqSelectExpr) {
        var ll = (SeqSelectExpr)lhs;
        ConstrainSubtypeRelation(ResolvedArrayType(ll.Seq.tok, 1, new InferredTypeProxy(), resolutionContext, true), ll.Seq.Type, ll.Seq,
          "LHS of array assignment must denote an array element (found {0})", ll.Seq.Type);
        if (!ll.SelectOne) {
          reporter.Error(MessageSource.Resolver, ll.Seq, "cannot assign to a range of array elements (try the 'forall' statement)");
        }
      } else if (lhs is MultiSelectExpr) {
        // nothing to check; this can only denote an array element
      } else {
        reporter.Error(MessageSource.Resolver, lhs, "LHS of assignment must denote a mutable variable or field");
      }
    }

    public void ResolveBlockStatement(BlockStmt blockStmt, ResolutionContext resolutionContext) {
      Contract.Requires(blockStmt != null);
      Contract.Requires(resolutionContext != null);

      if (blockStmt is DividedBlockStmt) {
        var div = (DividedBlockStmt)blockStmt;
        Contract.Assert(currentMethod is Constructor);  // divided bodies occur only in class constructors
        Contract.Assert(!resolutionContext.InFirstPhaseConstructor);  // divided bodies are never nested
        foreach (Statement ss in div.BodyInit) {
          ResolveStatementWithLabels(ss, resolutionContext with { InFirstPhaseConstructor = true });
        }
        foreach (Statement ss in div.BodyProper) {
          ResolveStatementWithLabels(ss, resolutionContext);
        }
      } else {
        foreach (Statement ss in blockStmt.Body) {
          ResolveStatementWithLabels(ss, resolutionContext);
        }
      }
    }

    public void ResolveStatementWithLabels(Statement stmt, ResolutionContext resolutionContext) {
      Contract.Requires(stmt != null);
      Contract.Requires(resolutionContext != null);

      enclosingStatementLabels.PushMarker();
      // push labels
      for (var l = stmt.Labels; l != null; l = l.Next) {
        var lnode = l.Data;
        Contract.Assert(lnode.Name != null);  // LabelNode's with .Label==null are added only during resolution of the break statements with 'stmt' as their target, which hasn't happened yet
        var prev = enclosingStatementLabels.Find(lnode.Name);
        if (prev == stmt) {
          reporter.Error(MessageSource.Resolver, lnode.Tok, "duplicate label");
        } else if (prev != null) {
          reporter.Error(MessageSource.Resolver, lnode.Tok, "label shadows an enclosing label");
        } else {
          var r = enclosingStatementLabels.Push(lnode.Name, stmt);
          Contract.Assert(r == Scope<Statement>.PushResult.Success);  // since we just checked for duplicates, we expect the Push to succeed
          if (DominatingStatementLabels.Find(lnode.Name) != null) {
            reporter.Error(MessageSource.Resolver, lnode.Tok, "label shadows a dominating label");
          } else {
            var rr = DominatingStatementLabels.Push(lnode.Name, lnode);
            Contract.Assert(rr == Scope<Label>.PushResult.Success);  // since we just checked for duplicates, we expect the Push to succeed
          }
        }
      }
      ResolveStatement(stmt, resolutionContext);
      enclosingStatementLabels.PopMarker();
    }

    void ResolveAlternatives(List<GuardedAlternative> alternatives, AlternativeLoopStmt loopToCatchBreaks, ResolutionContext resolutionContext) {
      Contract.Requires(alternatives != null);
      Contract.Requires(resolutionContext != null);

      // first, resolve the guards
      foreach (var alternative in alternatives) {
        int prevErrorCount = reporter.Count(ErrorLevel.Error);
        ResolveExpression(alternative.Guard, resolutionContext);
        Contract.Assert(alternative.Guard.Type != null);  // follows from postcondition of ResolveExpression
        bool successfullyResolved = reporter.Count(ErrorLevel.Error) == prevErrorCount;
        ConstrainTypeExprBool(alternative.Guard, "condition is expected to be of type bool, but is {0}");
      }

      if (loopToCatchBreaks != null) {
        loopStack.Add(loopToCatchBreaks);  // push
      }
      foreach (var alternative in alternatives) {
        scope.PushMarker();
        DominatingStatementLabels.PushMarker();
        if (alternative.IsBindingGuard) {
          var exists = (ExistsExpr)alternative.Guard;
          foreach (var v in exists.BoundVars) {
            ScopePushAndReport(scope, v, "bound-variable");
          }
        }
        ResolveAttributes(alternative, resolutionContext);
        foreach (Statement ss in alternative.Body) {
          ResolveStatementWithLabels(ss, resolutionContext);
        }
        DominatingStatementLabels.PopMarker();
        scope.PopMarker();
      }
      if (loopToCatchBreaks != null) {
        loopStack.RemoveAt(loopStack.Count - 1);  // pop
      }
    }

    /// <summary>
    /// Resolves the given call statement.
    /// Assumes all LHSs have already been resolved (and checked for mutability).
    /// </summary>
    void ResolveCallStmt(CallStmt s, ResolutionContext resolutionContext, Type receiverType) {
      Contract.Requires(s != null);
      Contract.Requires(resolutionContext != null);
      bool isInitCall = receiverType != null;

      var callee = s.Method;
      Contract.Assert(callee != null);  // follows from the invariant of CallStmt
      if (!isInitCall && callee is Constructor) {
        reporter.Error(MessageSource.Resolver, s, "a constructor is allowed to be called only when an object is being allocated");
      }

      // resolve left-hand sides (the right-hand sides are resolved below)
      foreach (var lhs in s.Lhs) {
        Contract.Assume(lhs.Type != null);  // a sanity check that LHSs have already been resolved
      }

      bool tryToResolve = false;
      if (callee.Outs.Count != s.Lhs.Count) {
        if (isInitCall) {
          reporter.Error(MessageSource.Resolver, s, "a method called as an initialization method must not have any result arguments");
        } else {
          reporter.Error(MessageSource.Resolver, s, "wrong number of method result arguments (got {0}, expected {1})", s.Lhs.Count, callee.Outs.Count);
          tryToResolve = true;
        }
      } else {
        if (isInitCall) {
          if (callee.IsStatic) {
            reporter.Error(MessageSource.Resolver, s.Tok, "a method called as an initialization method must not be 'static'");
          } else {
            tryToResolve = true;
          }
        } else if (!callee.IsStatic) {
          if (!scope.AllowInstance && s.Receiver is ThisExpr) {
            // The call really needs an instance, but that instance is given as 'this', which is not
            // available in this context.  For more details, see comment in the resolution of a
            // FunctionCallExpr.
            reporter.Error(MessageSource.Resolver, s.Receiver, "'this' is not allowed in a 'static' context");
          } else if (s.Receiver is StaticReceiverExpr) {
            reporter.Error(MessageSource.Resolver, s.Receiver, "call to instance method requires an instance");
          } else {
            tryToResolve = true;
          }
        } else {
          tryToResolve = true;
        }
      }

      if (tryToResolve) {
        var typeMap = s.MethodSelect.TypeArgumentSubstitutionsAtMemberDeclaration();
        // resolve arguments
        ResolveActualParameters(s.Bindings, callee.Ins, s.Tok, callee, resolutionContext, typeMap,
          callee.IsStatic ? null : s.Receiver);
        // type check the out-parameter arguments (in-parameters were type checked as part of ResolveActualParameters)
        for (int i = 0; i < callee.Outs.Count && i < s.Lhs.Count; i++) {
          var outFormal = callee.Outs[i];
          var it = outFormal.Type;
          Type st = it.Subst(typeMap);
          var lhs = s.Lhs[i];
          var what = GetLocationInformation(outFormal, callee.Outs.Count(), i, "method out-parameter");

          AddAssignableConstraint(
            s.Tok, lhs.Type, st,
            $"incorrect return type {what} (expected {{1}}, got {{0}})");
        }
        for (int i = 0; i < s.Lhs.Count; i++) {
          var lhs = s.Lhs[i];
          // LHS must denote a mutable field.
          CheckIsLvalue(lhs.Resolved, resolutionContext);
        }
      }
      if (Contract.Exists(callee.Decreases.Expressions, e => e is WildcardExpr) && !resolutionContext.CodeContext.AllowsNontermination) {
        reporter.Error(MessageSource.Resolver, s.Tok, "a call to a possibly non-terminating method is allowed only if the calling method is also declared (with 'decreases *') to be possibly non-terminating");
      }
    }

    /// <summary>
    /// Resolve the actual arguments given in "bindings". Then, check that there is exactly one
    /// actual for each formal, and impose assignable constraints.
    /// "typeMap" is applied to the type of each formal.
    /// This method should be called only once. That is, bindings.arguments is required to be null on entry to this method.
    /// </summary>
    void ResolveActualParameters(ActualBindings bindings, List<Formal> formals, IToken callTok, object context, ResolutionContext resolutionContext,
      Dictionary<TypeParameter, Type> typeMap, Expression/*?*/ receiver) {
      Contract.Requires(bindings != null);
      Contract.Requires(formals != null);
      Contract.Requires(callTok != null);
      Contract.Requires(context is Method || context is Function || context is DatatypeCtor || context is ArrowType);
      Contract.Requires(typeMap != null);
      Contract.Requires(!bindings.WasResolved);

      string whatKind;
      string name;
      if (context is Method cMethod) {
        whatKind = cMethod.WhatKind;
        name = $"{whatKind} '{cMethod.Name}'";
      } else if (context is Function cFunction) {
        whatKind = cFunction.WhatKind;
        name = $"{whatKind} '{cFunction.Name}'";
      } else if (context is DatatypeCtor cCtor) {
        whatKind = "datatype constructor";
        name = $"{whatKind} '{cCtor.Name}'";
      } else {
        var cArrowType = (ArrowType)context;
        whatKind = "function application";
        name = $"function type '{cArrowType}'";
      }

      // If all arguments are passed positionally, use simple error messages that talk about the count of arguments.
      var onlyPositionalArguments = bindings.ArgumentBindings.TrueForAll(binding => binding.FormalParameterName == null);
      var simpleErrorReported = false;
      if (onlyPositionalArguments) {
        var requiredParametersCount = formals.Count(f => f.DefaultValue == null);
        var actualsCounts = bindings.ArgumentBindings.Count;
        var sig = "";
        for (int i = 0; i < formals.Count; i++) {
          sig += (", " + formals[i].Name + ": " + formals[i].Type.ToString());
        }
        if (formals.Count > 0) {
          sig = ": (" + sig[2..] + ")";
        }
        if (requiredParametersCount <= actualsCounts && actualsCounts <= formals.Count) {
          // the situation is plausible
        } else if (requiredParametersCount == formals.Count) {
          // this is the common, classical case of no default parameter values; generate a straightforward error message
          reporter.Error(MessageSource.Resolver, callTok, $"wrong number of arguments (got {actualsCounts}, but {name} expects {formals.Count}{sig})");
          simpleErrorReported = true;
        } else if (actualsCounts < requiredParametersCount) {
          reporter.Error(MessageSource.Resolver, callTok, $"wrong number of arguments (got {actualsCounts}, but {name} expects at least {requiredParametersCount}{sig})");
          simpleErrorReported = true;
        } else {
          reporter.Error(MessageSource.Resolver, callTok, $"wrong number of arguments (got {actualsCounts}, but {name} expects at most {formals.Count}{sig})");
          simpleErrorReported = true;
        }
      }

      // resolve given arguments and populate the "namesToActuals" map
      var namesToActuals = new Dictionary<string, ActualBinding>();
      formals.ForEach(f => namesToActuals.Add(f.Name, null)); // a name mapping to "null" says it hasn't been filled in yet
      var stillAcceptingPositionalArguments = true;
      var bindingIndex = 0;
      foreach (var binding in bindings.ArgumentBindings) {
        var arg = binding.Actual;
        // insert the actual into "namesToActuals" under an appropriate name, unless there is an error
        if (binding.FormalParameterName != null) {
          var pname = binding.FormalParameterName.val;
          stillAcceptingPositionalArguments = false;
          if (!namesToActuals.TryGetValue(pname, out var b)) {
            reporter.Error(MessageSource.Resolver, binding.FormalParameterName, $"the binding named '{pname}' does not correspond to any formal parameter");
          } else if (b == null) {
            // all is good
            namesToActuals[pname] = binding;
          } else if (b.FormalParameterName == null) {
            reporter.Error(MessageSource.Resolver, binding.FormalParameterName, $"the parameter named '{pname}' is already given positionally");
          } else {
            reporter.Error(MessageSource.Resolver, binding.FormalParameterName, $"duplicate binding for parameter name '{pname}'");
          }
        } else if (!stillAcceptingPositionalArguments) {
          reporter.Error(MessageSource.Resolver, arg.tok, "a positional argument is not allowed to follow named arguments");
        } else if (bindingIndex < formals.Count) {
          // use the name of formal corresponding to this positional argument, unless the parameter is named-only
          var formal = formals[bindingIndex];
          var pname = formal.Name;
          if (formal.IsNameOnly) {
            reporter.Error(MessageSource.Resolver, arg.tok,
              $"nameonly parameter '{pname}' must be passed using a name binding; it cannot be passed positionally");
          }
          Contract.Assert(namesToActuals[pname] == null); // we expect this, since we've only filled parameters positionally so far
          namesToActuals[pname] = binding;
        } else {
          // too many positional arguments
          if (onlyPositionalArguments) {
            // error was reported before the "foreach" loop
            Contract.Assert(simpleErrorReported);
          } else if (formals.Count < bindingIndex) {
            // error was reported on a previous iteration of this "foreach" loop
          } else {
            reporter.Error(MessageSource.Resolver, callTok,
              $"wrong number of arguments ({name} expects {formals.Count}, got {bindings.ArgumentBindings.Count})");
          }
        }

        // resolve argument
        ResolveExpression(arg, resolutionContext);
        bindingIndex++;
      }

      var actuals = new List<Expression>();
      var formalIndex = 0;
      var substMap = new Dictionary<IVariable, Expression>();
      foreach (var formal in formals) {
        var b = namesToActuals[formal.Name];
        if (b != null) {
          actuals.Add(b.Actual);
          substMap.Add(formal, b.Actual);
          var what = GetLocationInformation(formal,
            bindings.ArgumentBindings.Count(), bindings.ArgumentBindings.IndexOf(b),
            whatKind + (context is Method ? " in-parameter" : " parameter"));

          AddAssignableConstraint(
            callTok, formal.Type.Subst(typeMap), b.Actual.Type,
            $"incorrect argument type {what} (expected {{0}}, found {{1}})");
        } else if (formal.DefaultValue != null) {
          // Note, in the following line, "substMap" is passed in, but it hasn't been fully filled in until the
          // end of this foreach loop. Still, that's soon enough, because DefaultValueExpression won't use it
          // until FillInDefaultValueExpressions at the end of Pass 1 of the Resolver.
          var n = new DefaultValueExpression(callTok, formal, receiver, substMap, typeMap);
          allDefaultValueExpressions.Add(n);
          actuals.Add(n);
          substMap.Add(formal, n);
        } else {
          // parameter has no value
          if (onlyPositionalArguments) {
            // a simple error message has already been reported
            Contract.Assert(simpleErrorReported);
          } else {
            var formalDescription = whatKind + (context is Method ? " in-parameter" : " parameter");
            var nameWithIndex = formal.HasName && formal is not ImplicitFormal ? "'" + formal.Name + "'" : "";
            if (formals.Count > 1 || nameWithIndex == "") {
              nameWithIndex += nameWithIndex == "" ? "" : " ";
              nameWithIndex += $"at index {formalIndex}";
            }
            var message = $"{formalDescription} {nameWithIndex} requires an argument of type {formal.Type}";
            reporter.Error(MessageSource.Resolver, callTok, message);
          }
        }
        formalIndex++;
      }

      bindings.AcceptArgumentExpressionsAsExactParameterList(actuals);
    }

    private static string GetLocationInformation(Formal parameter, int bindingCount, int bindingIndex, string formalDescription) {
      var displayName = parameter.HasName && parameter is not ImplicitFormal;
      var description = "";
      if (bindingCount > 1) {
        description += $"at index {bindingIndex} ";
      }

      description += $"for {formalDescription}";

      if (displayName) {
        description += $" '{parameter.Name}'";
      }

      return description;
    }

    /// <summary>
    /// To resolve "id" in expression "E . id", do:
    ///  * If E denotes a module name M:
    ///      0. Member of module M:  sub-module (including submodules of imports), class, datatype, etc.
    ///         (if two imported types have the same name, an error message is produced here)
    ///      1. Static member of M._default denoting an async task type
    ///    (Note that in contrast to ResolveNameSegment_Type, imported modules, etc. are ignored)
    ///  * If E denotes a type:
    ///      2. a. Member of that type denoting an async task type, or:
    ///         b. If allowDanglingDotName:
    ///            Return the type "E" and the given "expr", letting the caller try to make sense of the final dot-name.
    ///
    /// Note: 1 and 2a are not used now, but they will be of interest when async task types are supported.
    /// </summary>
    ResolveTypeReturn ResolveDotSuffix_Type(ExprDotName expr, ResolutionContext resolutionContext, bool allowDanglingDotName, ResolveTypeOption option, List<TypeParameter> defaultTypeArguments) {
      Contract.Requires(expr != null);
      Contract.Requires(!expr.WasResolved());
      Contract.Requires(expr.Lhs is NameSegment || expr.Lhs is ExprDotName);
      Contract.Requires(resolutionContext != null);
      Contract.Ensures(Contract.Result<ResolveTypeReturn>() == null || allowDanglingDotName);

      // resolve the LHS expression
      if (expr.Lhs is NameSegment) {
        ResolveNameSegment_Type((NameSegment)expr.Lhs, resolutionContext, option, defaultTypeArguments);
      } else {
        ResolveDotSuffix_Type((ExprDotName)expr.Lhs, resolutionContext, false, option, defaultTypeArguments);
      }

      if (expr.OptTypeArguments != null) {
        foreach (var ty in expr.OptTypeArguments) {
          ResolveType(expr.tok, ty, resolutionContext, option, defaultTypeArguments);
        }
      }

      Expression r = null;  // the resolved expression, if successful

      var lhs = expr.Lhs.Resolved;
      if (lhs != null && lhs.Type is Resolver_IdentifierExpr.ResolverType_Module) {
        var ri = (Resolver_IdentifierExpr)lhs;
        var sig = ((ModuleDecl)ri.Decl).AccessibleSignature(useCompileSignatures);
        sig = GetSignature(sig);
        // For 0:
        TopLevelDecl decl;

        if (sig.TopLevels.TryGetValue(expr.SuffixName, out decl)) {
          // ----- 0. Member of the specified module
          if (decl is AmbiguousTopLevelDecl) {
            var ad = (AmbiguousTopLevelDecl)decl;
            reporter.Error(MessageSource.Resolver, expr.tok, "The name {0} ambiguously refers to a type in one of the modules {1} (try qualifying the type name with the module name)", expr.SuffixName, ad.ModuleNames());
          } else {
            // We have found a module name or a type name.  We create a temporary expression that will never be seen by the compiler
            // or verifier, just to have a placeholder where we can recorded what we have found.
            r = CreateResolver_IdentifierExpr(expr.tok, expr.SuffixName, expr.OptTypeArguments, decl);
          }
#if ASYNC_TASK_TYPES
        } else if (sig.StaticMembers.TryGetValue(expr.SuffixName, out member)) {
          // ----- 1. static member of the specified module
          Contract.Assert(member.IsStatic); // moduleInfo.StaticMembers is supposed to contain only static members of the module's implicit class _default
          if (ReallyAmbiguousThing(ref member)) {
            reporter.Error(MessageSource.Resolver, expr.tok, "The name {0} ambiguously refers to a static member in one of the modules {1} (try qualifying the member name with the module name)", expr.SuffixName, ((AmbiguousMemberDecl)member).ModuleNames());
          } else {
            var receiver = new StaticReceiverExpr(expr.tok, (ClassDecl)member.EnclosingClass);
            r = ResolveExprDotCall(expr.tok, receiver, member, expr.OptTypeArguments, opts.resolutionContext, allowMethodCall);
          }
#endif
        } else {
          reporter.Error(MessageSource.Resolver, expr.tok, "module '{0}' does not declare a type '{1}'", ri.Decl.Name, expr.SuffixName);
        }

      } else if (lhs != null && lhs.Type is Resolver_IdentifierExpr.ResolverType_Type) {
        var ri = (Resolver_IdentifierExpr)lhs;
        // ----- 2. Look up name in type
        var ty = new UserDefinedType(ri.tok, ri.Decl.Name, ri.Decl, ri.TypeArgs);
        if (allowDanglingDotName && ty.IsRefType) {
          return new ResolveTypeReturn(ty, expr);
        }
        if (r == null) {
          reporter.Error(MessageSource.Resolver, expr.tok, "member '{0}' does not exist in type '{1}' or cannot be part of type name", expr.SuffixName, ri.Decl.Name);
        }
      }

      if (r == null) {
        // an error has been reported above; we won't fill in .ResolvedExpression, but we still must fill in .Type
        expr.Type = new InferredTypeProxy();
      } else {
        expr.ResolvedExpression = r;
        expr.Type = r.Type;
      }
      return null;
    }

    Resolver_IdentifierExpr CreateResolver_IdentifierExpr(IToken tok, string name, List<Type> optTypeArguments, TopLevelDecl decl) {
      Contract.Requires(tok != null);
      Contract.Requires(name != null);
      Contract.Requires(decl != null);
      Contract.Ensures(Contract.Result<Resolver_IdentifierExpr>() != null);

      if (!moduleInfo.IsAbstract) {
        if (decl is ModuleDecl md && md.Signature.IsAbstract) {
          reporter.Error(MessageSource.Resolver, tok, "a compiled module is not allowed to use an abstract module ({0})", decl.Name);
        }
      }
      var n = optTypeArguments == null ? 0 : optTypeArguments.Count;
      if (optTypeArguments != null) {
        // type arguments were supplied; they must be equal in number to those expected
        if (n != decl.TypeArgs.Count) {
          reporter.Error(MessageSource.Resolver, tok, "Wrong number of type arguments ({0} instead of {1}) passed to {2}: {3}", n, decl.TypeArgs.Count, decl.WhatKind, name);
        }
      }
      List<Type> tpArgs = new List<Type>();
      for (int i = 0; i < decl.TypeArgs.Count; i++) {
        tpArgs.Add(i < n ? optTypeArguments[i] : new InferredTypeProxy());
      }
      return new Resolver_IdentifierExpr(tok, decl, tpArgs);
    }

    public void ResolveStatement(Statement stmt, ResolutionContext resolutionContext) {
      Contract.Requires(stmt != null);
      Contract.Requires(resolutionContext != null);
      if (stmt is ICanResolve canResolve) {
        canResolve.Resolve(this, resolutionContext);
        return;
      }
      if (!(stmt is ForallStmt || stmt is ForLoopStmt)) {  // "forall" and "for" statements do their own attribute resolution below
        ResolveAttributes(stmt, resolutionContext);
      }
      if (stmt is PredicateStmt) {
        PredicateStmt s = (PredicateStmt)stmt;
        var assertStmt = stmt as AssertStmt;
        if (assertStmt != null && assertStmt.Label != null) {
          if (DominatingStatementLabels.Find(assertStmt.Label.Name) != null) {
            reporter.Error(MessageSource.Resolver, assertStmt.Label.Tok, "assert label shadows a dominating label");
          } else {
            var rr = DominatingStatementLabels.Push(assertStmt.Label.Name, assertStmt.Label);
            Contract.Assert(rr == Scope<Label>.PushResult.Success);  // since we just checked for duplicates, we expect the Push to succeed
          }
        }
        ResolveExpression(s.Expr, resolutionContext);
        Contract.Assert(s.Expr.Type != null);  // follows from postcondition of ResolveExpression
        ConstrainTypeExprBool(s.Expr, "condition is expected to be of type bool, but is {0}");
        if (assertStmt != null && assertStmt.Proof != null) {
          // clear the labels for the duration of checking the proof body, because break statements are not allowed to leave a the proof body
          var prevLblStmts = enclosingStatementLabels;
          var prevLoopStack = loopStack;
          enclosingStatementLabels = new Scope<Statement>();
          loopStack = new List<Statement>();
          ResolveStatement(assertStmt.Proof, resolutionContext);
          enclosingStatementLabels = prevLblStmts;
          loopStack = prevLoopStack;
        }
        var expectStmt = stmt as ExpectStmt;
        if (expectStmt != null) {
          if (expectStmt.Message == null) {
            expectStmt.Message = new StringLiteralExpr(s.Tok, "expectation violation", false);
          }
          ResolveExpression(expectStmt.Message, resolutionContext);
          Contract.Assert(expectStmt.Message.Type != null);  // follows from postcondition of ResolveExpression
        }

      } else if (stmt is PrintStmt) {
        var s = (PrintStmt)stmt;
        s.Args.Iter(e => ResolveExpression(e, resolutionContext));

      } else if (stmt is RevealStmt) {
        var s = (RevealStmt)stmt;
        foreach (var expr in s.Exprs) {
          var name = RevealStmt.SingleName(expr);
          var labeledAssert = name == null ? null : DominatingStatementLabels.Find(name) as AssertLabel;
          if (labeledAssert != null) {
            s.LabeledAsserts.Add(labeledAssert);
          } else {
            var revealResolutionContext = resolutionContext with { InReveal = true };
            if (expr is ApplySuffix) {
              var e = (ApplySuffix)expr;
              var methodCallInfo = ResolveApplySuffix(e, revealResolutionContext, true);
              if (methodCallInfo == null) {
                reporter.Error(MessageSource.Resolver, expr.tok, "expression has no reveal lemma");
              } else if (methodCallInfo.Callee.Member is TwoStateLemma && !revealResolutionContext.IsTwoState) {
                reporter.Error(MessageSource.Resolver, methodCallInfo.Tok, "a two-state function can only be revealed in a two-state context");
              } else if (methodCallInfo.Callee.AtLabel != null) {
                Contract.Assert(methodCallInfo.Callee.Member is TwoStateLemma);
                reporter.Error(MessageSource.Resolver, methodCallInfo.Tok, "to reveal a two-state function, do not list any parameters or @-labels");
              } else {
                var call = new CallStmt(s.RangeToken, new List<Expression>(), methodCallInfo.Callee, methodCallInfo.ActualParameters, methodCallInfo.Tok);
                s.ResolvedStatements.Add(call);
              }
            } else if (expr is NameSegment or ExprDotName) {
              if (expr is NameSegment) {
                ResolveNameSegment((NameSegment)expr, true, null, revealResolutionContext, true);
              } else {
                ResolveDotSuffix((ExprDotName)expr, true, null, revealResolutionContext, true);
              }
              MemberSelectExpr callee = (MemberSelectExpr)((ConcreteSyntaxExpression)expr).ResolvedExpression;
              if (callee == null) {
              } else if (callee.Member is Lemma or TwoStateLemma && Attributes.Contains(callee.Member.Attributes, "axiom")) {
                //The revealed member is a function
                reporter.Error(MessageSource.Resolver, callee.tok, "to reveal a function ({0}), append parentheses", callee.Member.ToString().Substring(7));
              } else {
                var call = new CallStmt(s.RangeToken, new List<Expression>(), callee, new List<ActualBinding>(), expr.tok);
                s.ResolvedStatements.Add(call);
              }
            } else {
              ResolveExpression(expr, revealResolutionContext);
            }
          }
        }
        foreach (var a in s.ResolvedStatements) {
          ResolveStatement(a, resolutionContext);
        }
      } else if (stmt is BreakStmt) {
        var s = (BreakStmt)stmt;
        if (s.TargetLabel != null) {
          Statement target = enclosingStatementLabels.Find(s.TargetLabel.val);
          if (target == null) {
            reporter.Error(MessageSource.Resolver, s.TargetLabel, $"{s.Kind} label is undefined or not in scope: {s.TargetLabel.val}");
          } else if (s.IsContinue && !(target is LoopStmt)) {
            reporter.Error(MessageSource.Resolver, s.TargetLabel, $"continue label must designate a loop: {s.TargetLabel.val}");
          } else {
            s.TargetStmt = target;
          }
        } else {
          Contract.Assert(1 <= s.BreakAndContinueCount); // follows from BreakStmt class invariant and the guard for this "else" branch
          var jumpStmt = s.BreakAndContinueCount == 1 ?
            $"a non-labeled '{s.Kind}' statement" :
            $"a '{Util.Repeat(s.BreakAndContinueCount - 1, "break ")}{s.Kind}' statement";
          if (loopStack.Count == 0) {
            reporter.Error(MessageSource.Resolver, s, $"{jumpStmt} is allowed only in loops");
          } else if (loopStack.Count < s.BreakAndContinueCount) {
            reporter.Error(MessageSource.Resolver, s,
              $"{jumpStmt} is allowed only in contexts with {s.BreakAndContinueCount} enclosing loops, but the current context only has {loopStack.Count}");
          } else {
            Statement target = loopStack[loopStack.Count - s.BreakAndContinueCount];
            if (target.Labels == null) {
              // make sure there is a label, because the compiler and translator will want to see a unique ID
              target.Labels = new LList<Label>(new Label(target.Tok, null), null);
            }
            s.TargetStmt = target;
          }
        }

      } else if (stmt is ProduceStmt) {
        var kind = stmt is YieldStmt ? "yield" : "return";
        if (stmt is YieldStmt && !(resolutionContext.CodeContext is IteratorDecl)) {
          reporter.Error(MessageSource.Resolver, stmt, "yield statement is allowed only in iterators");
        } else if (stmt is ReturnStmt && !(resolutionContext.CodeContext is Method)) {
          reporter.Error(MessageSource.Resolver, stmt, "return statement is allowed only in method");
        } else if (resolutionContext.InFirstPhaseConstructor) {
          reporter.Error(MessageSource.Resolver, stmt, "return statement is not allowed before 'new;' in a constructor");
        }
        var s = (ProduceStmt)stmt;
        if (s.Rhss != null) {
          var cmc = resolutionContext.CodeContext as IMethodCodeContext;
          if (cmc == null) {
            // an error has already been reported above
          } else if (cmc.Outs.Count != s.Rhss.Count) {
            reporter.Error(MessageSource.Resolver, s, "number of {2} parameters does not match declaration (found {0}, expected {1})", s.Rhss.Count, cmc.Outs.Count, kind);
          } else {
            Contract.Assert(s.Rhss.Count > 0);
            // Create a hidden update statement using the out-parameter formals, resolve the RHS, and check that the RHS is good.
            List<Expression> formals = new List<Expression>();
            foreach (Formal f in cmc.Outs) {
              Expression produceLhs;
              if (stmt is ReturnStmt) {
                var ident = new ImplicitIdentifierExpr(f.tok, f.Name);
                // resolve it here to avoid capture into more closely declared local variables
                ident.Var = f;
                ident.Type = ident.Var.Type;
                Contract.Assert(f.Type != null);
                produceLhs = ident;
              } else {
                var yieldIdent = new MemberSelectExpr(f.tok, new ImplicitThisExpr(f.tok), f.Name);
                ResolveExpression(yieldIdent, resolutionContext);
                produceLhs = yieldIdent;
              }
              formals.Add(produceLhs);
            }
            s.HiddenUpdate = new UpdateStmt(s.RangeToken, formals, s.Rhss, true);
            // resolving the update statement will check for return/yield statement specifics.
            ResolveStatement(s.HiddenUpdate, resolutionContext);
          }
        } else {// this is a regular return/yield statement.
          s.HiddenUpdate = null;
        }
      } else if (stmt is VarDeclStmt) {
        var s = (VarDeclStmt)stmt;
        // We have four cases.
        Contract.Assert(s.Update == null || s.Update is AssignSuchThatStmt || s.Update is UpdateStmt || s.Update is AssignOrReturnStmt);
        // 0.  There is no .Update.  This is easy, we will just resolve the locals.
        // 1.  The .Update is an AssignSuchThatStmt.  This is also straightforward:  first
        //     resolve the locals, which adds them to the scope, and then resolve the .Update.
        // 2.  The .Update is an UpdateStmt, which, resolved, means either a CallStmt or a bunch
        //     of parallel AssignStmt's.  Here, the right-hand sides should be resolved before
        //     the local variables have been added to the scope, but the left-hand sides should
        //     resolve to the newly introduced variables.
        // 3.  The .Update is a ":-" statement, for which resolution does two steps:
        //     First, desugar, then run the regular resolution on the desugared AST.
        // To accommodate these options, we first reach into the UpdateStmt, if any, to resolve
        // the left-hand sides of the UpdateStmt.  This will have the effect of shielding them
        // from a subsequent resolution (since expression resolution will do nothing if the .Type
        // field is already assigned.
        // Alright, so it is:

        // Resolve the types of the locals
        foreach (var local in s.Locals) {
          int prevErrorCount = reporter.Count(ErrorLevel.Error);
          ResolveType(local.Tok, local.OptionalType, resolutionContext, ResolveTypeOptionEnum.InferTypeProxies, null);
          if (reporter.Count(ErrorLevel.Error) == prevErrorCount) {
            local.type = local.OptionalType;
          } else {
            local.type = new InferredTypeProxy();
          }
        }
        // Resolve the UpdateStmt, if any
        if (s.Update is UpdateStmt) {
          var upd = (UpdateStmt)s.Update;
          // resolve the LHS
          Contract.Assert(upd.Lhss.Count == s.Locals.Count);
          for (int i = 0; i < upd.Lhss.Count; i++) {
            var local = s.Locals[i];
            var lhs = (IdentifierExpr)upd.Lhss[i];  // the LHS in this case will be an IdentifierExpr, because that's how the parser creates the VarDeclStmt
            Contract.Assert(lhs.Type == null);  // not yet resolved
            lhs.Var = local;
            lhs.Type = local.Type;
          }
          // resolve the whole thing
          s.Update.Resolve(this, resolutionContext);
        }

        if (s.Update is AssignOrReturnStmt) {
          var assignOrRet = (AssignOrReturnStmt)s.Update;
          // resolve the LHS
          Contract.Assert(assignOrRet.Lhss.Count == s.Locals.Count);
          for (int i = 0; i < s.Locals.Count; i++) {
            var local = s.Locals[i];
            var lhs = (IdentifierExpr)assignOrRet
              .Lhss[i]; // the LHS in this case will be an IdentifierExpr, because that's how the parser creates the VarDeclStmt
            Contract.Assert(lhs.Type == null); // not yet resolved
            lhs.Var = local;
            lhs.Type = local.Type;
          }

          // resolve the whole thing
          assignOrRet.Resolve(this, resolutionContext);
        }
        // Add the locals to the scope
        foreach (var local in s.Locals) {
          ScopePushAndReport(scope, local, "local-variable");
        }
        // With the new locals in scope, it's now time to resolve the attributes on all the locals
        foreach (var local in s.Locals) {
          ResolveAttributes(local, resolutionContext);
        }
        // Resolve the AssignSuchThatStmt, if any
        if (s.Update is AssignSuchThatStmt assignSuchThatStmt) {
          assignSuchThatStmt.Resolve(this, resolutionContext);
        }
        // Check on "assumption" variables
        foreach (var local in s.Locals) {
          if (Attributes.Contains(local.Attributes, "assumption")) {
            if (currentMethod != null) {
              ConstrainSubtypeRelation(Type.Bool, local.type, local.Tok, "assumption variable must be of type 'bool'");
              if (!local.IsGhost) {
                reporter.Error(MessageSource.Resolver, local.Tok, "assumption variable must be ghost");
              }
            } else {
              reporter.Error(MessageSource.Resolver, local.Tok, "assumption variable can only be declared in a method");
            }
          }
        }
      } else if (stmt is VarDeclPattern) {
        VarDeclPattern s = (VarDeclPattern)stmt;
        foreach (var local in s.LocalVars) {
          int prevErrorCount = reporter.Count(ErrorLevel.Error);
          ResolveType(local.Tok, local.OptionalType, resolutionContext, ResolveTypeOptionEnum.InferTypeProxies, null);
          if (reporter.Count(ErrorLevel.Error) == prevErrorCount) {
            local.type = local.OptionalType;
          } else {
            local.type = new InferredTypeProxy();
          }
        }
        ResolveExpression(s.RHS, resolutionContext);
        ResolveCasePattern(s.LHS, s.RHS.Type, resolutionContext);
        // Check for duplicate names now, because not until after resolving the case pattern do we know if identifiers inside it refer to bound variables or nullary constructors
        var c = 0;
        foreach (var bv in s.LHS.Vars) {
          ScopePushAndReport(scope, bv, "local_variable");
          c++;
        }
        if (c == 0) {
          // Every identifier-looking thing in the pattern resolved to a constructor; that is, this LHS is a constant literal
          reporter.Error(MessageSource.Resolver, s.LHS.tok, "LHS is a constant literal; to be legal, it must introduce at least one bound variable");
        }
      } else if (stmt is AssignStmt) {
        AssignStmt s = (AssignStmt)stmt;
        int prevErrorCount = reporter.Count(ErrorLevel.Error);
        ResolveExpression(s.Lhs, resolutionContext);  // allow ghosts for now, tighted up below
        bool lhsResolvedSuccessfully = reporter.Count(ErrorLevel.Error) == prevErrorCount;
        Contract.Assert(s.Lhs.Type != null);  // follows from postcondition of ResolveExpression
        // check that LHS denotes a mutable variable or a field
        var lhs = s.Lhs.Resolved;
        if (lhs is IdentifierExpr) {
          IVariable var = ((IdentifierExpr)lhs).Var;
          if (var == null) {
            // the LHS didn't resolve correctly; some error would already have been reported
          } else {
            CheckIsLvalue(lhs, resolutionContext);
          }
        } else if (lhs is MemberSelectExpr) {
          var fse = (MemberSelectExpr)lhs;
          if (fse.Member != null) {  // otherwise, an error was reported above
            CheckIsLvalue(fse, resolutionContext);
          }
        } else if (lhs is SeqSelectExpr) {
          var slhs = (SeqSelectExpr)lhs;
          // LHS is fine, provided the "sequence" is really an array
          if (lhsResolvedSuccessfully) {
            Contract.Assert(slhs.Seq.Type != null);
            CheckIsLvalue(slhs, resolutionContext);
          }
        } else if (lhs is MultiSelectExpr) {
          CheckIsLvalue(lhs, resolutionContext);
        } else {
          CheckIsLvalue(lhs, resolutionContext);
        }
        Type lhsType = s.Lhs.Type;
        if (s.Rhs is ExprRhs) {
          ExprRhs rr = (ExprRhs)s.Rhs;
          ResolveExpression(rr.Expr, resolutionContext);
          Contract.Assert(rr.Expr.Type != null);  // follows from postcondition of ResolveExpression

          if (s.Lhs is ImplicitIdentifierExpr { Var: Formal { InParam: false } }) {
            AddAssignableConstraint(stmt.Tok, lhsType, rr.Expr.Type, "Method return value mismatch (expected {0}, got {1})");
          } else {
            AddAssignableConstraint(stmt.Tok, lhsType, rr.Expr.Type, "RHS (of type {1}) not assignable to LHS (of type {0})");
          }
        } else if (s.Rhs is TypeRhs) {
          TypeRhs rr = (TypeRhs)s.Rhs;
          Type t = ResolveTypeRhs(rr, stmt, resolutionContext);
          AddAssignableConstraint(stmt.Tok, lhsType, t, "type {1} is not assignable to LHS (of type {0})");
        } else if (s.Rhs is HavocRhs) {
          // nothing else to do
        } else {
          Contract.Assert(false); throw new cce.UnreachableException();  // unexpected RHS
        }

      } else if (stmt is CallStmt) {
        CallStmt s = (CallStmt)stmt;
        ResolveCallStmt(s, resolutionContext, null);

      } else if (stmt is BlockStmt) {
        var s = (BlockStmt)stmt;
        scope.PushMarker();
        ResolveBlockStatement(s, resolutionContext);
        scope.PopMarker();

      } else if (stmt is IfStmt) {
        IfStmt s = (IfStmt)stmt;
        if (s.Guard != null) {
          ResolveExpression(s.Guard, resolutionContext);
          Contract.Assert(s.Guard.Type != null);  // follows from postcondition of ResolveExpression
          ConstrainTypeExprBool(s.Guard, "condition is expected to be of type bool, but is {0}");
        }

        scope.PushMarker();
        if (s.IsBindingGuard) {
          var exists = (ExistsExpr)s.Guard;
          foreach (var v in exists.BoundVars) {
            ScopePushAndReport(scope, v, "bound-variable");
          }
        }
        DominatingStatementLabels.PushMarker();
        ResolveBlockStatement(s.Thn, resolutionContext);
        DominatingStatementLabels.PopMarker();
        scope.PopMarker();

        if (s.Els != null) {
          DominatingStatementLabels.PushMarker();
          ResolveStatement(s.Els, resolutionContext);
          DominatingStatementLabels.PopMarker();
        }

      } else if (stmt is AlternativeStmt) {
        var s = (AlternativeStmt)stmt;
        ResolveAlternatives(s.Alternatives, null, resolutionContext);

      } else if (stmt is OneBodyLoopStmt) {
        var s = (OneBodyLoopStmt)stmt;
        var fvs = new HashSet<IVariable>();
        var usesHeap = false;
        if (s is WhileStmt whileS && whileS.Guard != null) {
          ResolveExpression(whileS.Guard, resolutionContext);
          Contract.Assert(whileS.Guard.Type != null);  // follows from postcondition of ResolveExpression
          FreeVariablesUtil.ComputeFreeVariables(whileS.Guard, fvs, ref usesHeap);
          ConstrainTypeExprBool(whileS.Guard, "condition is expected to be of type bool, but is {0}");
        } else if (s is ForLoopStmt forS) {
          var loopIndex = forS.LoopIndex;
          int prevErrorCount = reporter.Count(ErrorLevel.Error);
          ResolveType(loopIndex.Tok, loopIndex.Type, resolutionContext, ResolveTypeOptionEnum.InferTypeProxies, null);
          var err = new TypeConstraint.ErrorMsgWithToken(loopIndex.Tok, "index variable is expected to be of an integer type (got {0})", loopIndex.Type);
          ConstrainToIntegerType(loopIndex.Tok, loopIndex.Type, false, err);
          fvs.Add(loopIndex);

          ResolveExpression(forS.Start, resolutionContext);
          FreeVariablesUtil.ComputeFreeVariables(forS.Start, fvs, ref usesHeap);
          AddAssignableConstraint(forS.Start.tok, forS.LoopIndex.Type, forS.Start.Type, "lower bound (of type {1}) not assignable to index variable (of type {0})");
          if (forS.End != null) {
            ResolveExpression(forS.End, resolutionContext);
            FreeVariablesUtil.ComputeFreeVariables(forS.End, fvs, ref usesHeap);
            AddAssignableConstraint(forS.End.tok, forS.LoopIndex.Type, forS.End.Type, "upper bound (of type {1}) not assignable to index variable (of type {0})");
            if (forS.Decreases.Expressions.Count != 0) {
              reporter.Error(MessageSource.Resolver, forS.Decreases.Expressions[0].tok,
                "a 'for' loop is allowed an explicit 'decreases' clause only if the end-expression is '*'");
            }
          } else if (forS.Decreases.Expressions.Count == 0 && !resolutionContext.CodeContext.AllowsNontermination) {
            // note, the following error message is also emitted elsewhere (if the loop bears a "decreases *")
            reporter.Error(MessageSource.Resolver, forS.Tok,
              "a possibly infinite loop is allowed only if the enclosing method is declared (with 'decreases *') to be possibly non-terminating" +
              " (or you can add a 'decreases' clause to this 'for' loop if you want to prove that it does indeed terminate)");
          }

          // Create a new scope, add the local to the scope, and resolve the attributes
          scope.PushMarker();
          ScopePushAndReport(scope, loopIndex, "index-variable");
          ResolveAttributes(s, resolutionContext);
        }

        ResolveLoopSpecificationComponents(s.Invariants, s.Decreases, s.Mod, resolutionContext, fvs, ref usesHeap);

        if (s.Body != null) {
          loopStack.Add(s);  // push
          DominatingStatementLabels.PushMarker();
          ResolveStatement(s.Body, resolutionContext);
          DominatingStatementLabels.PopMarker();
          loopStack.RemoveAt(loopStack.Count - 1);  // pop
        } else {
          Contract.Assert(s.BodySurrogate == null);  // .BodySurrogate is set only once
          var loopFrame = new List<IVariable>();
          if (s is ForLoopStmt forLoopStmt) {
            loopFrame.Add(forLoopStmt.LoopIndex);
          }
          loopFrame.AddRange(fvs.Where(fv => fv.IsMutable));
          s.BodySurrogate = new WhileStmt.LoopBodySurrogate(loopFrame, usesHeap);
          var text = Util.Comma(s.BodySurrogate.LocalLoopTargets, fv => fv.Name);
          if (s.BodySurrogate.UsesHeap) {
            text += text.Length == 0 ? "$Heap" : ", $Heap";
          }
          text = string.Format("note, this loop has no body{0}", text.Length == 0 ? "" : " (loop frame: " + text + ")");
          reporter.Warning(MessageSource.Resolver, ErrorID.None, s.Tok, text);
        }

        if (s is ForLoopStmt) {
          scope.PopMarker();
        }

      } else if (stmt is AlternativeLoopStmt) {
        var s = (AlternativeLoopStmt)stmt;
        ResolveAlternatives(s.Alternatives, s, resolutionContext);
        var usesHeapDontCare = false;
        ResolveLoopSpecificationComponents(s.Invariants, s.Decreases, s.Mod, resolutionContext, null, ref usesHeapDontCare);

      } else if (stmt is ForallStmt) {
        var s = (ForallStmt)stmt;

        int prevErrorCount = reporter.Count(ErrorLevel.Error);
        scope.PushMarker();
        foreach (BoundVar v in s.BoundVars) {
          ScopePushAndReport(scope, v, "local-variable");
          ResolveType(v.tok, v.Type, resolutionContext, ResolveTypeOptionEnum.InferTypeProxies, null);
        }
        ResolveExpression(s.Range, resolutionContext);
        Contract.Assert(s.Range.Type != null);  // follows from postcondition of ResolveExpression
        ConstrainTypeExprBool(s.Range, "range restriction in forall statement must be of type bool (instead got {0})");
        foreach (var ens in s.Ens) {
          ResolveExpression(ens.E, resolutionContext);
          Contract.Assert(ens.E.Type != null);  // follows from postcondition of ResolveExpression
          ConstrainTypeExprBool(ens.E, "ensures condition is expected to be of type bool, but is {0}");
        }
        // Since the range and postconditions are more likely to infer the types of the bound variables, resolve them
        // first (above) and only then resolve the attributes (below).
        ResolveAttributes(s, resolutionContext);

        if (s.Body != null) {
          // clear the labels for the duration of checking the body, because break statements are not allowed to leave a forall statement
          var prevLblStmts = enclosingStatementLabels;
          var prevLoopStack = loopStack;
          enclosingStatementLabels = new Scope<Statement>();
          loopStack = new List<Statement>();
          ResolveStatement(s.Body, resolutionContext);
          enclosingStatementLabels = prevLblStmts;
          loopStack = prevLoopStack;
        } else {
          reporter.Warning(MessageSource.Resolver, ErrorID.None, s.Tok, "note, this forall statement has no body");
        }
        scope.PopMarker();

        if (prevErrorCount == reporter.Count(ErrorLevel.Error)) {
          // determine the Kind and run some additional checks on the body
          if (s.Ens.Count != 0) {
            // The only supported kind with ensures clauses is Proof.
            s.Kind = ForallStmt.BodyKind.Proof;
          } else {
            // There are three special cases:
            // * Assign, which is the only kind of the forall statement that allows a heap update.
            // * Call, which is a single call statement with no side effects or output parameters.
            // * A single calc statement, which is a special case of Proof where the postcondition can be inferred.
            // The effect of Assign and the postcondition of Call will be seen outside the forall
            // statement.
            Statement s0 = s.S0;
            if (s0 is AssignStmt) {
              s.Kind = ForallStmt.BodyKind.Assign;

              var rhs = ((AssignStmt)s0).Rhs;
              if (rhs is TypeRhs) {
                reporter.Error(MessageSource.Resolver, rhs.Tok, "new allocation not supported in aggregate assignments");
              }

            } else if (s0 is CallStmt) {
              s.Kind = ForallStmt.BodyKind.Call;
              var call = (CallStmt)s.S0;
              var method = call.Method;
              // if the called method is not in the same module as the ForallCall stmt
              // don't convert it to ForallExpression since the inlined called method's
              // ensure clause might not be resolved correctly(test\dafny3\GenericSort.dfy)
              if (method.EnclosingClass.EnclosingModuleDefinition != resolutionContext.CodeContext.EnclosingModule) {
                s.CanConvert = false;
              }
              // Additional information (namely, the postcondition of the call) will be reported later. But it cannot be
              // done yet, because the specification of the callee may not have been resolved yet.
            } else if (s0 is CalcStmt) {
              s.Kind = ForallStmt.BodyKind.Proof;
              // add the conclusion of the calc as a free postcondition
              var result = ((CalcStmt)s0).Result;
              s.Ens.Add(new AttributedExpression(result));
              reporter.Info(MessageSource.Resolver, s.Tok, "ensures " + Printer.ExprToString(result));
            } else {
              s.Kind = ForallStmt.BodyKind.Proof;
              if (s.Body is BlockStmt && ((BlockStmt)s.Body).Body.Count == 0) {
                // an empty statement, so don't produce any warning
              } else {
                reporter.Warning(MessageSource.Resolver, ErrorID.None, s.Tok, "the conclusion of the body of this forall statement will not be known outside the forall statement; consider using an 'ensures' clause");
              }
            }
          }

          if (s.ForallExpressions != null) {
            foreach (Expression expr in s.ForallExpressions) {
              ResolveExpression(expr, resolutionContext);
            }
          }
        }

      } else if (stmt is ModifyStmt) {
        var s = (ModifyStmt)stmt;
        ResolveAttributes(s.Mod, resolutionContext);
        foreach (FrameExpression fe in s.Mod.Expressions) {
          ResolveFrameExpression(fe, FrameExpressionUse.Modifies, resolutionContext);
        }
        if (s.Body != null) {
          ResolveBlockStatement(s.Body, resolutionContext);
        }

      } else if (stmt is CalcStmt) {
        var prevErrorCount = reporter.Count(ErrorLevel.Error);
        CalcStmt s = (CalcStmt)stmt;
        // figure out s.Op
        Contract.Assert(s.Op == null);  // it hasn't been set yet
        if (s.UserSuppliedOp != null) {
          s.Op = s.UserSuppliedOp;
        } else {
          // Usually, we'd use == as the default main operator.  However, if the calculation
          // begins or ends with a boolean literal, then we can do better by selecting ==>
          // or <==.  Also, if the calculation begins or ends with an empty set, then we can
          // do better by selecting <= or >=.
          if (s.Lines.Count == 0) {
            s.Op = CalcStmt.DefaultOp;
          } else {
            bool b;
            if (Expression.IsBoolLiteral(s.Lines.First(), out b)) {
              s.Op = new CalcStmt.BinaryCalcOp(b ? BinaryExpr.Opcode.Imp : BinaryExpr.Opcode.Exp);
            } else if (Expression.IsBoolLiteral(s.Lines.Last(), out b)) {
              s.Op = new CalcStmt.BinaryCalcOp(b ? BinaryExpr.Opcode.Exp : BinaryExpr.Opcode.Imp);
            } else if (Expression.IsEmptySetOrMultiset(s.Lines.First())) {
              s.Op = new CalcStmt.BinaryCalcOp(BinaryExpr.Opcode.Ge);
            } else if (Expression.IsEmptySetOrMultiset(s.Lines.Last())) {
              s.Op = new CalcStmt.BinaryCalcOp(BinaryExpr.Opcode.Le);
            } else {
              s.Op = CalcStmt.DefaultOp;
            }
          }
          reporter.Info(MessageSource.Resolver, s.Tok, s.Op.ToString());
        }

        if (s.Lines.Count > 0) {
          Type lineType = new InferredTypeProxy();
          var e0 = s.Lines.First();
          ResolveExpression(e0, resolutionContext);
          Contract.Assert(e0.Type != null);  // follows from postcondition of ResolveExpression
          var err = new TypeConstraint.ErrorMsgWithToken(e0.tok, "all lines in a calculation must have the same type (got {0} after {1})", e0.Type, lineType);
          ConstrainSubtypeRelation(lineType, e0.Type, err);
          for (int i = 1; i < s.Lines.Count; i++) {
            var e1 = s.Lines[i];
            ResolveExpression(e1, resolutionContext);
            Contract.Assert(e1.Type != null);  // follows from postcondition of ResolveExpression
            // reuse the error object if we're on the dummy line; this prevents a duplicate error message
            if (i < s.Lines.Count - 1) {
              err = new TypeConstraint.ErrorMsgWithToken(e1.tok, "all lines in a calculation must have the same type (got {0} after {1})", e1.Type, lineType);
            }
            ConstrainSubtypeRelation(lineType, e1.Type, err);
            var step = (s.StepOps[i - 1] ?? s.Op).StepExpr(e0, e1); // Use custom line operator
            ResolveExpression(step, resolutionContext);
            s.Steps.Add(step);
            e0 = e1;
          }

          // clear the labels for the duration of checking the hints, because break statements are not allowed to leave a forall statement
          var prevLblStmts = enclosingStatementLabels;
          var prevLoopStack = loopStack;
          enclosingStatementLabels = new Scope<Statement>();
          loopStack = new List<Statement>();
          foreach (var h in s.Hints) {
            foreach (var oneHint in h.Body) {
              DominatingStatementLabels.PushMarker();
              ResolveStatement(oneHint, resolutionContext);
              DominatingStatementLabels.PopMarker();
            }
          }
          enclosingStatementLabels = prevLblStmts;
          loopStack = prevLoopStack;

        }
        if (prevErrorCount == reporter.Count(ErrorLevel.Error) && s.Lines.Count > 0) {
          // do not build Result from the lines if there were errors, as it might be ill-typed and produce unnecessary resolution errors
          var resultOp = s.StepOps.Aggregate(s.Op, (op0, op1) => op1 == null ? op0 : op0.ResultOp(op1));
          s.Result = resultOp.StepExpr(s.Lines.First(), s.Lines.Last());
        } else {
          s.Result = CalcStmt.DefaultOp.StepExpr(Expression.CreateIntLiteral(s.Tok, 0), Expression.CreateIntLiteral(s.Tok, 0));
        }
        ResolveExpression(s.Result, resolutionContext);
        Contract.Assert(s.Result != null);
        Contract.Assert(prevErrorCount != reporter.Count(ErrorLevel.Error) || s.Steps.Count == s.Hints.Count);

      } else if (stmt is SkeletonStatement) {
        var s = (SkeletonStatement)stmt;
        reporter.Error(MessageSource.Resolver, s.Tok, "skeleton statements are allowed only in refining methods");
        // nevertheless, resolve the underlying statement; hey, why not
        if (s.S != null) {
          ResolveStatement(s.S, resolutionContext);
        }
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();
      }
    }

    private void ResolveLoopSpecificationComponents(List<AttributedExpression> invariants, Specification<Expression> decreases,
      Specification<FrameExpression> modifies, ResolutionContext resolutionContext, HashSet<IVariable> fvs, ref bool usesHeap) {
      Contract.Requires(invariants != null);
      Contract.Requires(decreases != null);
      Contract.Requires(modifies != null);
      Contract.Requires(resolutionContext != null);

      foreach (AttributedExpression inv in invariants) {
        ResolveAttributes(inv, resolutionContext);
        ResolveExpression(inv.E, resolutionContext);
        Contract.Assert(inv.E.Type != null);  // follows from postcondition of ResolveExpression
        if (fvs != null) {
          FreeVariablesUtil.ComputeFreeVariables(inv.E, fvs, ref usesHeap);
        }
        ConstrainTypeExprBool(inv.E, "invariant is expected to be of type bool, but is {0}");
      }

      ResolveAttributes(decreases, resolutionContext);
      foreach (Expression e in decreases.Expressions) {
        ResolveExpression(e, resolutionContext);
        if (e is WildcardExpr && !resolutionContext.CodeContext.AllowsNontermination) {
          reporter.Error(MessageSource.Resolver, e, "a possibly infinite loop is allowed only if the enclosing method is declared (with 'decreases *') to be possibly non-terminating");
        }
        if (fvs != null) {
          FreeVariablesUtil.ComputeFreeVariables(e, fvs, ref usesHeap);
        }
        // any type is fine
      }

      ResolveAttributes(modifies, resolutionContext);
      if (modifies.Expressions != null) {
        usesHeap = true;  // bearing a modifies clause counts as using the heap
        foreach (FrameExpression fe in modifies.Expressions) {
          ResolveFrameExpression(fe, FrameExpressionUse.Modifies, resolutionContext);
        }
      }
    }

    /// <summary>
    /// Resolves the default-valued expression for each formal in "formals".
    /// Solves the resulting type constraints.
    /// Assumes these are the only type constraints to be solved.
    ///
    /// Reports an error for any cyclic dependency among the default-value expressions of the formals.
    /// </summary>
    public void ResolveParameterDefaultValues(List<Formal> formals, ResolutionContext resolutionContext) {
      Contract.Requires(formals != null);
      Contract.Requires(resolutionContext != null);

      Contract.Assume(AllTypeConstraints.Count == 0);

      var dependencies = new Graph<IVariable>();
      var allowMoreRequiredParameters = true;
      var allowNamelessParameters = true;
      foreach (var formal in formals) {
        var d = formal.DefaultValue;
        if (d != null) {
          allowMoreRequiredParameters = false;
          ResolveExpression(d, resolutionContext);
          AddAssignableConstraint(d.tok, formal.Type, d.Type, "default-value expression (of type '{1}') is not assignable to formal (of type '{0}')");
          foreach (var v in FreeVariables(d)) {
            dependencies.AddEdge(formal, v);
          }
        } else if (!allowMoreRequiredParameters) {
          reporter.Error(MessageSource.Resolver, formal.tok, "a required parameter must precede all optional parameters");
        }
        if (!allowNamelessParameters && !formal.HasName) {
          reporter.Error(MessageSource.Resolver, formal.tok, "a nameless parameter must precede all nameonly parameters");
        }
        if (formal.IsNameOnly) {
          allowNamelessParameters = false;
        }
      }
      SolveAllTypeConstraints();

      foreach (var cycle in dependencies.AllCycles()) {
        var cy = Util.Comma(" -> ", cycle, v => v.Name) + " -> " + cycle[0].Name;
        reporter.Error(MessageSource.Resolver, cycle[0], $"default-value expressions for parameters contain a cycle: {cy}");
      }
    }

    /// <summary>
    /// See ResolveTypeOption for a description of the option/defaultTypeArguments parameters.
    /// </summary>
    public void ResolveType(IToken tok, Type type, ResolutionContext resolutionContext, ResolveTypeOptionEnum eopt, List<TypeParameter> defaultTypeArguments) {
      Contract.Requires(tok != null);
      Contract.Requires(type != null);
      Contract.Requires(resolutionContext != null);
      Contract.Requires(eopt != ResolveTypeOptionEnum.AllowPrefixExtend);
      ResolveType(tok, type, resolutionContext, new ResolveTypeOption(eopt), defaultTypeArguments);
    }

    public void ResolveType(IToken tok, Type type, ICodeContext topLevelContext, ResolveTypeOptionEnum eopt, List<TypeParameter> defaultTypeArguments) {
      ResolveType(tok, type, ResolutionContext.FromCodeContext(topLevelContext), eopt, defaultTypeArguments);
    }

    public void ResolveType(IToken tok, Type type, ICodeContext topLevelContext, ResolveTypeOption option, List<TypeParameter> defaultTypeArguments) {
      ResolveType(tok, type, ResolutionContext.FromCodeContext(topLevelContext), option, defaultTypeArguments);
    }

    public void ResolveType(IToken tok, Type type, ResolutionContext resolutionContext, ResolveTypeOption option, List<TypeParameter> defaultTypeArguments) {
      Contract.Requires(tok != null);
      Contract.Requires(type != null);
      Contract.Requires(resolutionContext != null);
      Contract.Requires(option != null);
      Contract.Requires((option.Opt == ResolveTypeOptionEnum.DontInfer || option.Opt == ResolveTypeOptionEnum.InferTypeProxies) == (defaultTypeArguments == null));
      var r = ResolveTypeLenient(tok, type, resolutionContext, option, defaultTypeArguments, false);
      Contract.Assert(r == null);
    }

    public class ResolveTypeReturn {
      public readonly Type ReplacementType;
      public readonly ExprDotName LastComponent;
      public ResolveTypeReturn(Type replacementType, ExprDotName lastComponent) {
        Contract.Requires(replacementType != null);
        Contract.Requires(lastComponent != null);
        ReplacementType = replacementType;
        LastComponent = lastComponent;
      }
    }
    /// <summary>
    /// See ResolveTypeOption for a description of the option/defaultTypeArguments parameters.
    /// One more thing:  if "allowDanglingDotName" is true, then if the resolution would have produced
    ///   an error message that could have been avoided if "type" denoted an identifier sequence one
    ///   shorter, then return an unresolved replacement type where the identifier sequence is one
    ///   shorter.  (In all other cases, the method returns null.)
    /// </summary>
    public ResolveTypeReturn ResolveTypeLenient(IToken tok, Type type, ResolutionContext resolutionContext, ResolveTypeOption option, List<TypeParameter> defaultTypeArguments, bool allowDanglingDotName) {
      Contract.Requires(tok != null);
      Contract.Requires(type != null);
      Contract.Requires(resolutionContext != null);
      Contract.Requires((option.Opt == ResolveTypeOptionEnum.DontInfer || option.Opt == ResolveTypeOptionEnum.InferTypeProxies) == (defaultTypeArguments == null));
      if (type is BitvectorType) {
        var t = (BitvectorType)type;
        // nothing to resolve, but record the fact that this bitvector width is in use
        builtIns.Bitwidths.Add(t.Width);
      } else if (type is BasicType) {
        // nothing to resolve
      } else if (type is MapType) {
        var mt = (MapType)type;
        var errorCount = reporter.Count(ErrorLevel.Error);
        int typeArgumentCount;
        if (mt.HasTypeArg()) {
          ResolveType(tok, mt.Domain, resolutionContext, option, defaultTypeArguments);
          ResolveType(tok, mt.Range, resolutionContext, option, defaultTypeArguments);
          typeArgumentCount = 2;
        } else if (option.Opt == ResolveTypeOptionEnum.DontInfer) {
          mt.SetTypeArgs(new InferredTypeProxy(), new InferredTypeProxy());
          typeArgumentCount = 0;
        } else {
          var inferredTypeArgs = new List<Type>();
          FillInTypeArguments(tok, 2, inferredTypeArgs, defaultTypeArguments, option);
          Contract.Assert(inferredTypeArgs.Count <= 2);
          if (inferredTypeArgs.Count == 1) {
            mt.SetTypeArgs(inferredTypeArgs[0], new InferredTypeProxy());
            typeArgumentCount = 1;
          } else if (inferredTypeArgs.Count == 2) {
            mt.SetTypeArgs(inferredTypeArgs[0], inferredTypeArgs[1]);
            typeArgumentCount = 2;
          } else {
            mt.SetTypeArgs(new InferredTypeProxy(), new InferredTypeProxy());
            typeArgumentCount = 0;
          }
        }
        // defaults and auto have been applied; check if we now have the right number of arguments
        if (2 != typeArgumentCount) {
          reporter.Error(MessageSource.Resolver, tok, "Wrong number of type arguments ({0} instead of 2) passed to type: {1}", typeArgumentCount, mt.CollectionTypeName);
        }
      } else if (type is CollectionType) {
        var t = (CollectionType)type;
        var errorCount = reporter.Count(ErrorLevel.Error);
        if (t.HasTypeArg()) {
          ResolveType(tok, t.Arg, resolutionContext, option, defaultTypeArguments);
        } else if (option.Opt != ResolveTypeOptionEnum.DontInfer) {
          var inferredTypeArgs = new List<Type>();
          FillInTypeArguments(tok, 1, inferredTypeArgs, defaultTypeArguments, option);
          if (inferredTypeArgs.Count != 0) {
            Contract.Assert(inferredTypeArgs.Count == 1);
            t.SetTypeArg(inferredTypeArgs[0]);
          }
        }
        if (!t.HasTypeArg()) {
          // defaults and auto have been applied; check if we now have the right number of arguments
          reporter.Error(MessageSource.Resolver, tok, "Wrong number of type arguments (0 instead of 1) passed to type: {0}", t.CollectionTypeName);
          // add a proxy type, to make sure that CollectionType will have have a non-null Arg
          t.SetTypeArg(new InferredTypeProxy());
        }

      } else if (type is UserDefinedType) {
        var t = (UserDefinedType)type;
        if (t.ResolvedClass != null) {
          // Apparently, this type has already been resolved
          return null;
        }
        var prevErrorCount = reporter.Count(ErrorLevel.Error);
        if (t.NamePath is ExprDotName) {
          var ret = ResolveDotSuffix_Type((ExprDotName)t.NamePath, resolutionContext, allowDanglingDotName, option, defaultTypeArguments);
          if (ret != null) {
            return ret;
          }
        } else {
          var s = (NameSegment)t.NamePath;
          ResolveNameSegment_Type(s, resolutionContext, option, defaultTypeArguments);
        }
        if (reporter.Count(ErrorLevel.Error) == prevErrorCount) {
          var r = t.NamePath.Resolved as Resolver_IdentifierExpr;
          if (r == null || !(r.Type is Resolver_IdentifierExpr.ResolverType_Type)) {
            reporter.Error(MessageSource.Resolver, t.tok, "expected type");
          } else if (r.Type is Resolver_IdentifierExpr.ResolverType_Type) {
            var d = r.Decl;
            if (d is OpaqueTypeDecl) {
              // resolve like a type parameter, and it may have type parameters if it's an opaque type
              t.ResolvedClass = d;  // Store the decl, so the compiler will generate the fully qualified name
            } else if (d is RedirectingTypeDecl) {
              var dd = (RedirectingTypeDecl)d;
              var caller = CodeContextWrapper.Unwrap(resolutionContext.CodeContext) as ICallable;
              if (caller != null && !(d is SubsetTypeDecl && caller is SpecialFunction)) {
                if (caller != d) {
                } else if (d is TypeSynonymDecl && !(d is SubsetTypeDecl)) {
                  // detect self-loops here, since they don't show up in the graph's SCC methods
                  reporter.Error(MessageSource.Resolver, d.tok, "type-synonym cycle: {0} -> {0}", d.Name);
                } else {
                  // detect self-loops here, since they don't show up in the graph's SCC methods
                  reporter.Error(MessageSource.Resolver, d.tok, "recursive constraint dependency involving a {0}: {1} -> {1}", d.WhatKind, d.Name);
                }
              }
              t.ResolvedClass = d;
            } else if (d is DatatypeDecl) {
              t.ResolvedClass = d;
            } else {
              // d is a type parameter, coinductive datatype, or class, and it may have type parameters
              t.ResolvedClass = d;
            }
            if (option.Opt == ResolveTypeOptionEnum.DontInfer) {
              // don't add anything
            } else if (d.TypeArgs.Count != t.TypeArgs.Count && t.TypeArgs.Count == 0) {
              FillInTypeArguments(t.tok, d.TypeArgs.Count, t.TypeArgs, defaultTypeArguments, option);
            }
            // defaults and auto have been applied; check if we now have the right number of arguments
            if (d.TypeArgs.Count != t.TypeArgs.Count) {
              reporter.Error(MessageSource.Resolver, t.tok, "Wrong number of type arguments ({0} instead of {1}) passed to {2}: {3}", t.TypeArgs.Count, d.TypeArgs.Count, d.WhatKind, t.Name);
            }

          }
        }
        if (t.ResolvedClass == null) {
          // There was some error. Still, we will set .ResolvedClass to some value to prevent some crashes in the downstream resolution.  The
          // 0-tuple is convenient, because it is always in scope.
          t.ResolvedClass = builtIns.TupleType(t.tok, 0, false);
          // clear out the TypeArgs since 0-tuple doesn't take TypeArg
          t.TypeArgs = new List<Type>();
        }

      } else if (type is TypeProxy) {
        TypeProxy t = (TypeProxy)type;
        if (t.T != null) {
          ResolveType(tok, t.T, resolutionContext, option, defaultTypeArguments);
        }
      } else if (type is SelfType) {
        // do nothing.
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected type
      }
      return null;
    }

    /// <summary>
    /// Adds to "typeArgs" a list of "n" type arguments, possibly extending "defaultTypeArguments".
    /// </summary>
    static void FillInTypeArguments(IToken tok, int n, List<Type> typeArgs, List<TypeParameter> defaultTypeArguments, ResolveTypeOption option) {
      Contract.Requires(tok != null);
      Contract.Requires(0 <= n);
      Contract.Requires(typeArgs != null && typeArgs.Count == 0);
      if (option.Opt == ResolveTypeOptionEnum.InferTypeProxies) {
        // add type arguments that will be inferred
        for (int i = 0; i < n; i++) {
          typeArgs.Add(new InferredTypeProxy());
        }
      } else if (option.Opt == ResolveTypeOptionEnum.AllowPrefix && defaultTypeArguments.Count < n) {
        // there aren't enough default arguments, so don't do anything
      } else {
        // we'll add arguments
        if (option.Opt == ResolveTypeOptionEnum.AllowPrefixExtend) {
          // extend defaultTypeArguments, if needed
          for (int i = defaultTypeArguments.Count; i < n; i++) {
            var tp = new TypeParameter(tok.ToRange(), new Name(tok.ToRange(), "_T" + i), i, option.Parent);
            if (option.Parent is IteratorDecl) {
              tp.Characteristics.AutoInit = Type.AutoInitInfo.CompilableValue;
            }
            defaultTypeArguments.Add(tp);
          }
        }
        Contract.Assert(n <= defaultTypeArguments.Count);
        // automatically supply a prefix of the arguments from defaultTypeArguments
        for (int i = 0; i < n; i++) {
          typeArgs.Add(new UserDefinedType(defaultTypeArguments[i]));
        }
      }
    }

    public static bool TypeConstraintsIncludeProxy(Type t, TypeProxy proxy) {
      return TypeConstraintsIncludeProxy_Aux(t, proxy, new HashSet<TypeProxy>());
    }
    static bool TypeConstraintsIncludeProxy_Aux(Type t, TypeProxy proxy, ISet<TypeProxy> visited) {
      Contract.Requires(t != null);
      Contract.Requires(!(t is TypeProxy) || ((TypeProxy)t).T == null);  // t is expected to have been normalized first
      Contract.Requires(proxy != null && proxy.T == null);
      Contract.Requires(visited != null);
      var tproxy = t as TypeProxy;
      if (tproxy != null) {
        if (object.ReferenceEquals(tproxy, proxy)) {
          return true;
        } else if (visited.Contains(tproxy)) {
          return false;
        }
        visited.Add(tproxy);
        foreach (var su in tproxy.Subtypes) {
          if (TypeConstraintsIncludeProxy_Aux(su, proxy, visited)) {
            return true;
          }
        }
        foreach (var su in tproxy.Supertypes) {
          if (TypeConstraintsIncludeProxy_Aux(su, proxy, visited)) {
            return true;
          }
        }
      } else {
        // check type arguments of t
        foreach (var ta in t.TypeArgs) {
          var a = ta.Normalize();
          if (TypeConstraintsIncludeProxy_Aux(a, proxy, visited)) {
            return true;
          }
        }
      }
      return false;
    }

    public Type ResolveTypeRhs(TypeRhs rr, Statement stmt, ResolutionContext resolutionContext) {
      Contract.Requires(rr != null);
      Contract.Requires(stmt != null);
      Contract.Requires(resolutionContext != null);
      Contract.Ensures(Contract.Result<Type>() != null);

      if (rr.Type == null) {
        if (rr.ArrayDimensions != null) {
          // ---------- new T[EE]    OR    new T[EE] (elementInit)
          Contract.Assert(rr.Bindings == null && rr.Path == null && rr.InitCall == null);
          ResolveType(stmt.Tok, rr.EType, resolutionContext, ResolveTypeOptionEnum.InferTypeProxies, null);
          int i = 0;
          foreach (Expression dim in rr.ArrayDimensions) {
            Contract.Assert(dim != null);
            ResolveExpression(dim, resolutionContext);
            ConstrainToIntegerType(dim, false, string.Format("new must use an integer-based expression for the array size (got {{0}}{0})", rr.ArrayDimensions.Count == 1 ? "" : " for index " + i));
            i++;
          }
          rr.Type = ResolvedArrayType(stmt.Tok, rr.ArrayDimensions.Count, rr.EType, resolutionContext, false);
          if (rr.ElementInit != null) {
            ResolveExpression(rr.ElementInit, resolutionContext);
            // Check
            //     int^N -> rr.EType  :>  rr.ElementInit.Type
            builtIns.CreateArrowTypeDecl(rr.ArrayDimensions.Count);  // TODO: should this be done already in the parser?
            var args = new List<Type>();
            for (int ii = 0; ii < rr.ArrayDimensions.Count; ii++) {
              args.Add(builtIns.Nat());
            }
            var arrowType = new ArrowType(rr.ElementInit.tok, builtIns.ArrowTypeDecls[rr.ArrayDimensions.Count], args, rr.EType);
            var lambdaType = rr.ElementInit.Type.AsArrowType;
            if (lambdaType != null && lambdaType.TypeArgs[0] is InferredTypeProxy) {
              (lambdaType.TypeArgs[0] as InferredTypeProxy).KeepConstraints = true;
            }
            string underscores;
            if (rr.ArrayDimensions.Count == 1) {
              underscores = "_";
            } else {
              underscores = "(" + Util.Comma(rr.ArrayDimensions.Count, x => "_") + ")";
            }
            var hintString = string.Format(" (perhaps write '{0} =>' in front of the expression you gave in order to make it an arrow type)", underscores);
            ConstrainSubtypeRelation(arrowType, rr.ElementInit.Type, rr.ElementInit, "array-allocation initialization expression expected to have type '{0}' (instead got '{1}'){2}",
              arrowType, rr.ElementInit.Type, new LazyString_OnTypeEquals(rr.EType, rr.ElementInit.Type, hintString));
          } else if (rr.InitDisplay != null) {
            foreach (var v in rr.InitDisplay) {
              ResolveExpression(v, resolutionContext);
              AddAssignableConstraint(v.tok, rr.EType, v.Type, "initial value must be assignable to array's elements (expected '{0}', got '{1}')");
            }
          }
        } else {
          bool callsConstructor = false;
          if (rr.Bindings == null) {
            ResolveType(stmt.Tok, rr.EType, resolutionContext, ResolveTypeOptionEnum.InferTypeProxies, null);
            var cl = (rr.EType as UserDefinedType)?.ResolvedClass as NonNullTypeDecl;
            if (cl != null && !(rr.EType.IsTraitType && !rr.EType.NormalizeExpand().IsObjectQ)) {
              // life is good
            } else {
              reporter.Error(MessageSource.Resolver, rr.tok, "new can be applied only to class types (got {0})", rr.EType);
            }
          } else {
            string initCallName = null;
            IToken initCallTok = null;
            // Resolve rr.Path and do one of three things:
            // * If rr.Path denotes a type, then set EType,initCallName to rr.Path,"_ctor", which sets up a call to the anonymous constructor.
            // * If the all-but-last components of rr.Path denote a type, then do EType,initCallName := allButLast(EType),last(EType)
            // * Otherwise, report an error
            var ret = ResolveTypeLenient(rr.Tok, rr.Path, resolutionContext, new ResolveTypeOption(ResolveTypeOptionEnum.InferTypeProxies), null, true);
            if (ret != null) {
              // The all-but-last components of rr.Path denote a type (namely, ret.ReplacementType).
              rr.EType = ret.ReplacementType;
              initCallName = ret.LastComponent.SuffixName;
              initCallTok = ret.LastComponent.tok;
            } else {
              // Either rr.Path resolved correctly as a type or there was no way to drop a last component to make it into something that looked
              // like a type.  In either case, set EType,initCallName to Path,"_ctor" and continue.
              rr.EType = rr.Path;
              initCallName = "_ctor";
              initCallTok = rr.Tok;
            }
            var cl = (rr.EType as UserDefinedType)?.ResolvedClass as NonNullTypeDecl;
            if (cl == null || rr.EType.IsTraitType) {
              reporter.Error(MessageSource.Resolver, rr.tok, "new can be applied only to class types (got {0})", rr.EType);
            } else {
              // ---------- new C.Init(EE)
              Contract.Assert(initCallName != null);
              var prevErrorCount = reporter.Count(ErrorLevel.Error);

              // We want to create a MemberSelectExpr for the initializing method.  To do that, we create a throw-away receiver of the appropriate
              // type, create an dot-suffix expression around this receiver, and then resolve it in the usual way for dot-suffix expressions.
              var lhs = new ImplicitThisExpr_ConstructorCall(initCallTok) { Type = rr.EType };
              var callLhs = new ExprDotName(((UserDefinedType)rr.EType).tok, lhs, initCallName, ret == null ? null : ret.LastComponent.OptTypeArguments);
              ResolveDotSuffix(callLhs, true, rr.Bindings.ArgumentBindings, resolutionContext, true);
              if (prevErrorCount == reporter.Count(ErrorLevel.Error)) {
                Contract.Assert(callLhs.ResolvedExpression is MemberSelectExpr);  // since ResolveApplySuffix succeeded and call.Lhs denotes an expression (not a module or a type)
                var methodSel = (MemberSelectExpr)callLhs.ResolvedExpression;
                if (methodSel.Member is Method) {
                  rr.InitCall = new CallStmt(stmt.RangeToken, new List<Expression>(), methodSel, rr.Bindings.ArgumentBindings, initCallTok);
                  ResolveCallStmt(rr.InitCall, resolutionContext, rr.EType);
                  if (rr.InitCall.Method is Constructor) {
                    callsConstructor = true;
                  }
                } else {
                  reporter.Error(MessageSource.Resolver, initCallTok, "object initialization must denote an initializing method or constructor ({0})", initCallName);
                }
              }
            }
          }
          if (rr.EType.IsRefType) {
            var udt = rr.EType.NormalizeExpand() as UserDefinedType;
            if (udt != null) {
              var cl = (ClassDecl)udt.ResolvedClass;  // cast is guaranteed by the call to rr.EType.IsRefType above, together with the "rr.EType is UserDefinedType" test
              if (!callsConstructor && !cl.IsObjectTrait && !udt.IsArrayType && (cl.HasConstructor || cl.EnclosingModuleDefinition != currentClass.EnclosingModuleDefinition)) {
                reporter.Error(MessageSource.Resolver, stmt, "when allocating an object of {1}type '{0}', one of its constructor methods must be called", cl.Name,
                  cl.HasConstructor ? "" : "imported ");
              }
            }
          }
          rr.Type = rr.EType;
        }
      }
      return rr.Type;
    }

    /// <summary>
    /// Resolve "memberName" in what currently is known as "receiverType". If "receiverType" is an unresolved
    /// proxy type, try to solve enough type constraints and use heuristics to figure out which type contains
    /// "memberName" and return that enclosing type as "tentativeReceiverType". However, try not to make
    /// type-inference decisions about "receiverType"; instead, lay down the further constraints that need to
    /// be satisfied in order for "tentativeReceiverType" to be where "memberName" is found.
    /// Consequently, if "memberName" is found and returned as a "MemberDecl", it may still be the case that
    /// "receiverType" is an unresolved proxy type and that, after solving more type constraints, "receiverType"
    /// eventually gets set to a type more specific than "tentativeReceiverType".
    /// </summary>
    public MemberDecl ResolveMember(IToken tok, Type receiverType, string memberName, out NonProxyType tentativeReceiverType) {
      Contract.Requires(tok != null);
      Contract.Requires(receiverType != null);
      Contract.Requires(memberName != null);
      Contract.Ensures(Contract.Result<MemberDecl>() == null || Contract.ValueAtReturn(out tentativeReceiverType) != null);

      receiverType = PartiallyResolveTypeForMemberSelection(tok, receiverType, memberName);

      if (receiverType is TypeProxy) {
        reporter.Error(MessageSource.Resolver, tok, "type of the receiver is not fully determined at this program point", receiverType);
        tentativeReceiverType = null;
        return null;
      }
      Contract.Assert(receiverType is NonProxyType);  // there are only two kinds of types: proxies and non-proxies

      foreach (var valuet in valuetypeDecls) {
        if (valuet.IsThisType(receiverType)) {
          MemberDecl member;
          if (valuet.Members.TryGetValue(memberName, out member)) {
            SelfType resultType = null;
            if (member is SpecialFunction) {
              resultType = ((SpecialFunction)member).ResultType as SelfType;
            } else if (member is SpecialField) {
              resultType = ((SpecialField)member).Type as SelfType;
            }
            if (resultType != null) {
              SelfTypeSubstitution = new Dictionary<TypeParameter, Type>();
              SelfTypeSubstitution.Add(resultType.TypeArg, receiverType);
              resultType.ResolvedType = receiverType;
            }
            tentativeReceiverType = (NonProxyType)receiverType;
            return member;
          }
          break;
        }
      }

      var ctype = receiverType.NormalizeExpand() as UserDefinedType;
      var cd = ctype?.AsTopLevelTypeWithMembersBypassInternalSynonym;
      if (cd != null) {
        Contract.Assert(ctype.TypeArgs.Count == cd.TypeArgs.Count);  // follows from the fact that ctype was resolved
        MemberDecl member;
        if (!classMembers[cd].TryGetValue(memberName, out member)) {
          if (memberName == "_ctor") {
            reporter.Error(MessageSource.Resolver, tok, "{0} {1} does not have an anonymous constructor", cd.WhatKind, cd.Name);
          } else {
            reporter.Error(MessageSource.Resolver, tok, "member '{0}' does not exist in {2} '{1}'", memberName, cd.Name, cd.WhatKind);
          }
        } else if (!VisibleInScope(member)) {
          reporter.Error(MessageSource.Resolver, tok, "member '{0}' has not been imported in this scope and cannot be accessed here", memberName);
        } else {
          tentativeReceiverType = ctype;
          return member;
        }
        tentativeReceiverType = null;
        return null;
      }

      reporter.Error(MessageSource.Resolver, tok, "type {0} does not have a member {1}", receiverType, memberName);
      tentativeReceiverType = null;
      return null;
    }

    /// <summary>
    /// Roughly speaking, tries to figure out the head of the type of "t", making as few inference decisions as possible.
    /// More precisely, returns a type that contains all the members of "t"; or if "memberName" is non-null, a type
    /// that at least contains the member "memberName" of "t".  Typically, this type is the head type of "t",
    /// but it may also be a type in a super- or subtype relation to "t".
    /// In some cases, it is necessary to make some inference decisions in order to figure out the type to return.
    /// </summary>
    public Type PartiallyResolveTypeForMemberSelection(IToken tok, Type t, string memberName = null, int strength = 0) {
      Contract.Requires(tok != null);
      Contract.Requires(t != null);
      Contract.Ensures(Contract.Result<Type>() != null);
      Contract.Ensures(!(Contract.Result<Type>() is TypeProxy) || ((TypeProxy)Contract.Result<Type>()).T == null);
      t = t.NormalizeExpand();
      if (!(t is TypeProxy)) {
        return t;  // we're good
      }

      // simplify constraints
      PrintTypeConstraintState(10);
      if (strength > 0) {
        var proxySpecializations = new HashSet<TypeProxy>();
        GetRelatedTypeProxies(t, proxySpecializations);
        var anyNewConstraintsAssignable = ConvertAssignableToSubtypeConstraints(proxySpecializations);
        var anyNewConstraintsEquatable = TightenUpEquatable(proxySpecializations);
        if ((strength > 1 && !anyNewConstraintsAssignable && !anyNewConstraintsEquatable) || strength == 10) {
          if (t is TypeProxy) {
            // One more try
            var r = GetBaseTypeFromProxy((TypeProxy)t, new Dictionary<TypeProxy, Type>());
            if (r != null) {
              if (DafnyOptions.O.TypeInferenceDebug) {
                Console.WriteLine("  ----> found improvement through GetBaseTypeFromProxy: {0}", r);
              }
              return r;
            }
          }

          if (DafnyOptions.O.TypeInferenceDebug) {
            Console.WriteLine("  ----> found no improvement, giving up");
          }
          return t;
        }
      }
      PartiallySolveTypeConstraints(false);
      PrintTypeConstraintState(11);
      t = t.NormalizeExpandKeepConstraints();
      var proxy = t as TypeProxy;
      if (proxy == null) {
        return t;  // simplification did the trick
      }
      if (DafnyOptions.O.TypeInferenceDebug) {
        Console.WriteLine("DEBUG: Member selection{3}:  {1} :> {0} :> {2}", t,
          Util.Comma(proxy.SupertypesKeepConstraints, su => su.ToString()),
          Util.Comma(proxy.SubtypesKeepConstraints, su => su.ToString()),
          memberName == null ? "" : " (" + memberName + ")");
      }

      // Look for a join of head symbols among the proxy's subtypes
      Type joinType = null;
      if (JoinOfAllSubtypes(proxy, ref joinType, new HashSet<TypeProxy>()) && joinType != null) {
        DetermineRootLeaf(joinType, out _, out _, out var headIsRoot, out _);
        if (joinType.IsDatatype) {
          if (DafnyOptions.O.TypeInferenceDebug) {
            Console.WriteLine("  ----> join is a datatype: {0}", joinType);
          }
          ConstrainSubtypeRelation(t, joinType, tok, "Member selection requires a supertype of {0} (got something more like {1})", t, joinType);
          return joinType;
        } else if (headIsRoot) {
          // we're good to go -- by picking "join" (whose type parameters have been replaced by fresh proxies), we're not losing any generality
          if (DafnyOptions.O.TypeInferenceDebug) {
            Console.WriteLine("  ----> improved to {0} through join", joinType);
          }
          AssignProxyAndHandleItsConstraints(proxy, joinType, true);
          return proxy.NormalizeExpand();  // we return proxy.T instead of join, in case the assignment gets hijacked
        } else if (memberName == "_#apply" || memberName == "requires" || memberName == "reads") {
          var generalArrowType = joinType.AsArrowType;  // go all the way to the base type, to get to the general arrow type, if any0
          if (generalArrowType != null) {
            // pick the supertype "generalArrowType" of "join"
            if (DafnyOptions.O.TypeInferenceDebug) {
              Console.WriteLine("  ----> improved to {0} through join and function application", generalArrowType);
            }
            ConstrainSubtypeRelation(generalArrowType, t, tok, "Function application requires a subtype of {0} (got something more like {1})", generalArrowType, t);
            return generalArrowType;
          }
        } else if (memberName != null) {
          // If "join" has a member called "memberName" and no supertype of "join" does, then we'll pick this join
          if (joinType.IsRefType) {
            var joinExpanded = joinType.NormalizeExpand();  // go all the way to the base type, to get to the class
            if (!joinExpanded.IsObjectQ) {
              var cl = ((UserDefinedType)joinExpanded).ResolvedClass as ClassDecl;
              if (cl != null) {
                // TODO: the following could be improved by also supplying an upper bound of the search (computed as a join of the supertypes)
                var plausibleMembers = new HashSet<MemberDecl>();
                FindAllMembers(cl, memberName, plausibleMembers);
                if (plausibleMembers.Count == 1) {
                  var mbr = plausibleMembers.First();
                  if (mbr.EnclosingClass == cl) {
                    if (DafnyOptions.O.TypeInferenceDebug) {
                      Console.WriteLine("  ----> improved to {0} through member-selection join", joinType);
                    }
                    var joinRoot = joinType.NormalizeExpand();  // blow passed any constraints
                    ConstrainSubtypeRelation(joinRoot, t, tok, "Member selection requires a subtype of {0} (got something more like {1})", joinRoot, t);
                    return joinType;
                  } else {
                    // pick the supertype "mbr.EnclosingClass" of "cl"
                    Contract.Assert(mbr.EnclosingClass is TraitDecl);  // a proper supertype of a ClassDecl must be a TraitDecl
                    var typeMapping = cl.ParentFormalTypeParametersToActuals;
                    TopLevelDecl td = mbr.EnclosingClass;
                    foreach (var tt in cl.TraitAncestors()) {
                      // If there is a match, the list of Type actuals is unique
                      // (a class cannot inherit both Trait<T1> and Trait<T2> with T1 != T2).
                      if (tt == (TraitDecl)mbr.EnclosingClass) {
                        td = tt;
                      }
                    }
                    List<Type> proxyTypeArgs = td.TypeArgs.ConvertAll(t0 => typeMapping.ContainsKey(t0) ? typeMapping[t0] : (Type)new InferredTypeProxy());
                    var joinMapping = TypeParameter.SubstitutionMap(cl.TypeArgs, joinType.TypeArgs);
                    proxyTypeArgs = proxyTypeArgs.ConvertAll(t0 => t0.Subst(joinMapping));
                    proxyTypeArgs = proxyTypeArgs.ConvertAll(t0 => t0.AsTypeParameter == null ? t0 : (Type)new InferredTypeProxy());
                    var pickItFromHere = new UserDefinedType(tok, mbr.EnclosingClass.Name, mbr.EnclosingClass, proxyTypeArgs);
                    if (DafnyOptions.O.TypeInferenceDebug) {
                      Console.WriteLine("  ----> improved to {0} through join and member lookup", pickItFromHere);
                    }
                    ConstrainSubtypeRelation(pickItFromHere, t, tok, "Member selection requires a subtype of {0} (got something more like {1})", pickItFromHere, t);
                    return pickItFromHere;
                  }
                }
              }
            }
          }
        }
        if (DafnyOptions.O.TypeInferenceDebug) {
          Console.WriteLine("  ----> found no improvement, because join does not determine type enough");
        }
      }

      // Compute the meet of the proxy's supertypes
      Type meet = null;
      if (MeetOfAllSupertypes(proxy, ref meet, new HashSet<TypeProxy>(), false) && meet != null) {
        // If the meet does have the member, then this looks promising. It could be that the
        // type would get further constrained later to pick some subtype (in particular, a
        // subclass that overrides the member) of this meet. But this is the best we can do
        // now.
        if (meet is TypeProxy) {
          if (proxy == meet.Normalize()) {
            // can this really ever happen?
            if (DafnyOptions.O.TypeInferenceDebug) {
              Console.WriteLine("  ----> found no improvement (other than the proxy itself)");
            }
            return t;
          } else {
            if (DafnyOptions.O.TypeInferenceDebug) {
              Console.WriteLine("  ----> (merging, then trying to improve further) assigning proxy {0}.T := {1}", proxy, meet);
            }
            Contract.Assert(proxy != meet);
            proxy.T = meet;
            Contract.Assert(t.NormalizeExpand() == meet);
            return PartiallyResolveTypeForMemberSelection(tok, t, memberName, strength + 1);
          }
        }
        if (!(meet is ArtificialType)) {
          if (DafnyOptions.O.TypeInferenceDebug) {
            Console.WriteLine("  ----> improved to {0} through meet", meet);
          }
          if (memberName != null) {
            AssignProxyAndHandleItsConstraints(proxy, meet, true);
            return proxy.NormalizeExpand(); // we return proxy.T instead of meet, in case the assignment gets hijacked
          } else {
            return meet;
          }
        }
      }

      // as a last resort, act on any artificial type nearby the proxy
      var artificialSuper = proxy.InClusterOfArtificial(AllXConstraints);
      if (artificialSuper != null) {
        if (DafnyOptions.O.TypeInferenceDebug) {
          Console.WriteLine("  ----> use artificial supertype: {0}", artificialSuper);
        }
        return artificialSuper;
      }

      // we weren't able to do it
      if (DafnyOptions.O.TypeInferenceDebug) {
        Console.WriteLine("  ----> found no improvement using simple things, trying harder once more");
      }
      return PartiallyResolveTypeForMemberSelection(tok, t, memberName, strength + 1);
    }

    private Type/*?*/ GetBaseTypeFromProxy(TypeProxy proxy, Dictionary<TypeProxy, Type/*?*/> determinedProxies) {
      Contract.Requires(proxy != null);
      Contract.Requires(determinedProxies != null);
      Type t;
      if (determinedProxies.TryGetValue(proxy, out t)) {
        // "t" may be null (meaning search for "proxy" is underway or was unsuccessful) or non-null (search for
        // "proxy" has completed successfully), but we return it in either case
        return t;
      }
      determinedProxies.Add(proxy, null);  // record that search for "proxy" is underway
      // First, go through subtype constraints, treating each as if it were an equality
      foreach (var c in AllTypeConstraints) {
        t = GetBaseTypeFromProxy_Eq(proxy, c.Super, c.Sub, determinedProxies);
        if (t != null) {
          determinedProxies[proxy] = t;
          return t;
        }
      }
      // Next, check XConstraints that can be seen as equality constraints
      foreach (var xc in AllXConstraints) {
        switch (xc.ConstraintName) {
          case "Assignable":
          case "Equatable":
          case "EquatableArg":
            t = GetBaseTypeFromProxy_Eq(proxy, xc.Types[0], xc.Types[1], determinedProxies);
            if (t != null) {
              determinedProxies[proxy] = t;
              return t;
            }
            break;
          case "InSet":
            // etc. TODO
            break;
          default:
            break;
        }
      }
      return null;
    }
    /// <summary>
    /// Tries to find a non-proxy type corresponding to "proxy", under the assumption that "t" equals "u" and
    /// "determinedProxies" assumptions.  In the process, may add to "determinedProxies".
    /// </summary>
    private Type/*?*/ GetBaseTypeFromProxy_Eq(TypeProxy proxy, Type t, Type u, Dictionary<TypeProxy, Type/*?*/> determinedProxies) {
      Contract.Requires(proxy != null);
      Contract.Requires(determinedProxies != null);
      Contract.Requires(t != null);
      Contract.Requires(u != null);
      t = t.NormalizeExpand();
      u = u.NormalizeExpand();
      return GetBaseTypeFromProxy_EqAux(proxy, t, u, determinedProxies) ?? GetBaseTypeFromProxy_EqAux(proxy, u, t, determinedProxies);
    }
    private Type/*?*/ GetBaseTypeFromProxy_EqAux(TypeProxy proxy, Type t, Type u, Dictionary<TypeProxy, Type/*?*/> determinedProxies) {
      Contract.Requires(proxy != null);
      Contract.Requires(determinedProxies != null);
      Contract.Requires(t != null && (!(t is TypeProxy) || ((TypeProxy)t).T == null));
      Contract.Requires(u != null && (!(u is TypeProxy) || ((TypeProxy)u).T == null));
      if (t == proxy) {
        if (u is TypeProxy) {
          return GetBaseTypeFromProxy((TypeProxy)u, determinedProxies);
        } else {
          return u;
        }
      } else if (t.ContainsProxy(proxy)) {
        if (u is TypeProxy) {
          u = GetBaseTypeFromProxy((TypeProxy)u, determinedProxies);
          if (u == null) {
            return null;
          }
        }
        if (Type.SameHead(t, u)) {
          Contract.Assert(t.TypeArgs.Count == u.TypeArgs.Count);
          for (int i = 0; i < t.TypeArgs.Count; i++) {
            var r = GetBaseTypeFromProxy_Eq(proxy, t.TypeArgs[i], u.TypeArgs[i], determinedProxies);
            if (r != null) {
              return r;
            }
          }
        }
      }
      return null;
    }

    private void GetRelatedTypeProxies(Type t, ISet<TypeProxy> proxies) {
      Contract.Requires(t != null);
      Contract.Requires(proxies != null);
      var proxy = t.Normalize() as TypeProxy;
      if (proxy == null || proxies.Contains(proxy)) {
        return;
      }
      if (DafnyOptions.O.TypeInferenceDebug) {
        Console.WriteLine("DEBUG: GetRelatedTypeProxies: finding {0} interesting", proxy);
      }
      proxies.Add(proxy);
      // close over interesting constraints
      foreach (var c in AllTypeConstraints) {
        var super = c.Super.Normalize();
        if (super.TypeArgs.Exists(ta => ta.Normalize() == proxy)) {
          GetRelatedTypeProxies(c.Sub, proxies);
        }
      }
      foreach (var xc in AllXConstraints) {
        var xc0 = xc.Types[0].Normalize();
        if (xc.ConstraintName == "Assignable" && (xc0 == proxy || xc0.TypeArgs.Exists(ta => ta.Normalize() == proxy))) {
          GetRelatedTypeProxies(xc.Types[1], proxies);
        } else if (xc.ConstraintName == "Innable" && xc.Types[1].Normalize() == proxy) {
          GetRelatedTypeProxies(xc.Types[0], proxies);
        } else if ((xc.ConstraintName == "ModifiesFrame" || xc.ConstraintName == "ReadsFrame") && xc.Types[1].Normalize() == proxy) {
          GetRelatedTypeProxies(xc.Types[0], proxies);
        }
      }
    }

    /// <summary>
    /// Attempts to compute the join of "join", "t", and all of "t"'s known subtype( constraint)s.  The join
    /// ignores type parameters.  It is assumed that "join" on entry already includes the join of all proxies
    /// in "visited". The empty join is represented by "null".
    /// The return is "true" if the join exists.
    /// </summary>
    bool JoinOfAllSubtypes(Type t, ref Type joinType, ISet<TypeProxy> visited) {
      Contract.Requires(t != null);
      Contract.Requires(visited != null);

      t = t.NormalizeExpandKeepConstraints();

      var proxy = t as TypeProxy;
      if (proxy != null) {
        if (visited.Contains(proxy)) {
          return true;
        }
        visited.Add(proxy);

        foreach (var c in proxy.SubtypeConstraints) {
          var s = c.Sub.NormalizeExpandKeepConstraints();
          if (!JoinOfAllSubtypes(s, ref joinType, visited)) {
            return false;
          }
        }
        if (joinType == null) {
          // also consider "Assignable" constraints
          foreach (var c in AllXConstraints) {
            if (c.ConstraintName == "Assignable" && c.Types[0].Normalize() == proxy) {
              var s = c.Types[1].NormalizeExpandKeepConstraints();
              if (!JoinOfAllSubtypes(s, ref joinType, visited)) {
                return false;
              }
            }
          }
        }
        return true;
      }

      if (joinType == null) {
        // stick with what we've got
        joinType = t;
        return true;
      } else if (Type.IsHeadSupertypeOf(joinType, t)) {
        // stick with what we've got
        return true;
      } else if (Type.IsHeadSupertypeOf(t, joinType)) {
        joinType = Type.HeadWithProxyArgs(t);
        return true;
      } else {
        joinType = Type.Join(joinType, Type.HeadWithProxyArgs(t), builtIns);  // the only way this can succeed is if we obtain a (non-null or nullable) trait
        Contract.Assert(joinType == null ||
                        joinType.IsObjectQ || joinType.IsObject ||
                        (joinType is UserDefinedType udt && (udt.ResolvedClass is TraitDecl || (udt.ResolvedClass is NonNullTypeDecl nntd && nntd.Class is TraitDecl))));
        return joinType != null;
      }
    }

    /// <summary>
    /// Attempts to compute the meet of "meet", all of "t"'s known supertype( constraint)s, and, if "includeT"
    /// and "t" has no supertype( constraint)s, "t".
    /// The meet ignores type parameters. (Really?? --KRML)
    /// It is assumed that "meet" on entry already includes the meet of all proxies
    /// in "visited". The empty meet is represented by "null".
    /// The return is "true" if the meet exists.
    /// </summary>
    bool MeetOfAllSupertypes(Type t, ref Type meet, ISet<TypeProxy> visited, bool includeT) {
      Contract.Requires(t != null);
      Contract.Requires(visited != null);

      t = t.NormalizeExpandKeepConstraints();
      var proxy = t as TypeProxy;
      if (proxy != null) {
        if (visited.Contains(proxy)) {
          return true;
        }
        visited.Add(proxy);

        var delegatedToOthers = false;
        foreach (var c in proxy.SupertypeConstraints) {
          var s = c.Super.NormalizeExpandKeepConstraints();
          delegatedToOthers = true;
          if (!MeetOfAllSupertypes(s, ref meet, visited, true)) {
            return false;
          }
        }
        if (!delegatedToOthers) {
          // also consider "Assignable" constraints
          foreach (var c in AllXConstraints) {
            if (c.ConstraintName == "Assignable" && c.Types[1].Normalize() == proxy) {
              var s = c.Types[0].NormalizeExpandKeepConstraints();
              delegatedToOthers = true;
              if (!MeetOfAllSupertypes(s, ref meet, visited, true)) {
                return false;
              }
            }
          }
        }
        if (delegatedToOthers) {
          return true;
        } else if (!includeT) {
          return true;
        } else if (meet == null || meet.Normalize() == proxy) {
          meet = proxy;
          return true;
        } else {
          return false;
        }
      }

      if (meet == null) {
        meet = Type.HeadWithProxyArgs(t);
        return true;
      } else if (Type.IsHeadSupertypeOf(t, meet)) {
        // stick with what we've got
        return true;
      } else if (Type.IsHeadSupertypeOf(meet, t)) {
        meet = Type.HeadWithProxyArgs(t);
        return true;
      } else {
        meet = Type.Meet(meet, Type.HeadWithProxyArgs(t), builtIns);
        return meet != null;
      }
    }

    /// <summary>
    /// Check that the type uses formal type parameters in a way that is agreeable with their variance specifications.
    /// "context == Co" says that "type" is allowed to vary in the positive direction.
    /// "context == Contra" says that "type" is allowed to vary in the negative direction.
    /// "context == Non" says that "type" must not vary at all.
    /// * "lax" says that the context is not strict -- type parameters declared to be strict must not be used in a lax context
    /// </summary>
    public void CheckVariance(Type type, ICallable enclosingTypeDefinition, TypeParameter.TPVariance context, bool lax) {
      Contract.Requires(type != null);
      Contract.Requires(enclosingTypeDefinition != null);

      type = type.Normalize();  // we keep constraints, since subset types have their own type-parameter variance specifications; we also keep synonys, since that gives rise to better error messages
      if (type is BasicType) {
        // fine
      } else if (type is MapType) {
        var t = (MapType)type;
        // If its an infinite map, the domain's context is lax
        CheckVariance(t.Domain, enclosingTypeDefinition, context, lax || !t.Finite);
        CheckVariance(t.Range, enclosingTypeDefinition, context, lax);
      } else if (type is SetType) {
        var t = (SetType)type;
        // If its an infinite set, the argument's context is lax
        CheckVariance(t.Arg, enclosingTypeDefinition, context, lax || !t.Finite);
      } else if (type is CollectionType) {
        var t = (CollectionType)type;
        CheckVariance(t.Arg, enclosingTypeDefinition, context, lax);
      } else if (type is UserDefinedType) {
        var t = (UserDefinedType)type;
        if (t.ResolvedClass is TypeParameter tp) {
          if (tp.Variance != TypeParameter.TPVariance.Non && tp.Variance != context) {
            reporter.Error(MessageSource.Resolver, t.tok, "formal type parameter '{0}' is not used according to its variance specification", tp.Name);
          } else if (tp.StrictVariance && lax) {
            string hint;
            if (tp.VarianceSyntax == TypeParameter.TPVarianceSyntax.NonVariant_Strict) {
              hint = string.Format(" (perhaps try declaring '{0}' as '-{0}' or '!{0}')", tp.Name);
            } else {
              Contract.Assert(tp.VarianceSyntax == TypeParameter.TPVarianceSyntax.Covariant_Strict);
              hint = string.Format(" (perhaps try changing the declaration from '+{0}' to '*{0}')", tp.Name);
            }
            reporter.Error(MessageSource.Resolver, t.tok, "formal type parameter '{0}' is not used according to its variance specification (it is used left of an arrow){1}", tp.Name, hint);
          }
        } else {
          var resolvedClass = t.ResolvedClass;
          Contract.Assert(resolvedClass != null);  // follows from that the given type was successfully resolved
          Contract.Assert(resolvedClass.TypeArgs.Count == t.TypeArgs.Count);
          if (lax) {
            // we have to be careful about uses of the type being defined
            var cg = enclosingTypeDefinition.EnclosingModule.CallGraph;
            var t0 = resolvedClass as ICallable;
            if (t0 != null && cg.GetSCCRepresentative(t0) == cg.GetSCCRepresentative(enclosingTypeDefinition)) {
              reporter.Error(MessageSource.Resolver, t.tok, "using the type being defined ('{0}') here would cause a logical inconsistency by defining a type whose cardinality exceeds itself (like the Continuum Transfunctioner, you might say its power would then be exceeded only by its mystery)", resolvedClass.Name);
            }
          }
          for (int i = 0; i < t.TypeArgs.Count; i++) {
            Type p = t.TypeArgs[i];
            var tpFormal = resolvedClass.TypeArgs[i];
            CheckVariance(p, enclosingTypeDefinition,
              context == TypeParameter.TPVariance.Non ? context :
              context == TypeParameter.TPVariance.Co ? tpFormal.Variance :
              TypeParameter.Negate(tpFormal.Variance),
              lax || !tpFormal.StrictVariance);
          }
        }
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected type
      }
    }

    /// <summary>
    /// See ConstrainToIntegerType description for the overload above.
    /// </summary>
    void ConstrainToIntegerType(IToken tok, Type type, bool allowBitVector, TypeConstraint.ErrorMsg errorMsg) {
      Contract.Requires(tok != null);
      Contract.Requires(type != null);
      Contract.Requires(errorMsg != null);
      // We do two constraints: the first can aid in determining types, but allows bit-vectors; the second excludes bit-vectors.
      // However, we reuse the error message, so that only one error gets reported.
      ConstrainSubtypeRelation(new IntVarietiesSupertype(), type, errorMsg);
      if (!allowBitVector) {
        AddXConstraint(tok, "IntegerType", type, errorMsg);
      }
    }

    /// <summary>
    /// Attempts to rewrite a datatype update into more primitive operations, after doing the appropriate resolution checks.
    /// Upon success, returns that rewritten expression and sets "legalSourceConstructors".
    /// Upon some resolution error, return null.
    ///
    /// Actually, the method returns two expressions (or returns "(null, null)"). The first expression is the desugaring to be
    /// used when the DatatypeUpdateExpr is used in a ghost context. The second is to be used for a compiled context. In either
    /// case, "legalSourceConstructors" contains both ghost and compiled constructors.
    ///
    /// The reason for computing both desugarings here is that it's too early to tell if the DatatypeUpdateExpr is being used in
    /// a ghost or compiled context. This is a consequence of doing the deguaring so early. But it's also convenient to do the
    /// desugaring during resolution, because then the desugaring can be constructed as a non-resolved expression on which ResolveExpression
    /// is called--this is easier than constructing an already-resolved expression.
    /// </summary>
    (Expression, Expression) ResolveDatatypeUpdate(IToken tok, Expression root, DatatypeDecl dt, List<Tuple<IToken, string, Expression>> memberUpdates,
      ResolutionContext resolutionContext, out List<MemberDecl> members, out List<DatatypeCtor> legalSourceConstructors) {
      Contract.Requires(tok != null);
      Contract.Requires(root != null);
      Contract.Requires(dt != null);
      Contract.Requires(memberUpdates != null);
      Contract.Requires(resolutionContext != null);

      legalSourceConstructors = null;
      members = new List<MemberDecl>();

      // First, compute the list of candidate result constructors, that is, the constructors
      // that have all of the mentioned destructors. Issue errors for duplicated names and for
      // names that are not destructors in the datatype.
      var candidateResultCtors = dt.Ctors;  // list of constructors that have all the so-far-mentioned destructors
      var memberNames = new HashSet<string>();
      var rhsBindings = new Dictionary<string, Tuple<BoundVar/*let variable*/, IdentifierExpr/*id expr for let variable*/, Expression /*RHS in given syntax*/>>();
      var subst = TypeParameter.SubstitutionMap(dt.TypeArgs, root.Type.NormalizeExpand().TypeArgs);
      foreach (var entry in memberUpdates) {
        var destructor_str = entry.Item2;
        if (memberNames.Contains(destructor_str)) {
          reporter.Error(MessageSource.Resolver, entry.Item1, "duplicate update member '{0}'", destructor_str);
        } else {
          memberNames.Add(destructor_str);
          MemberDecl member;
          if (!classMembers[dt].TryGetValue(destructor_str, out member)) {
            reporter.Error(MessageSource.Resolver, entry.Item1, "member '{0}' does not exist in datatype '{1}'", destructor_str, dt.Name);
          } else if (!(member is DatatypeDestructor)) {
            reporter.Error(MessageSource.Resolver, entry.Item1, "member '{0}' is not a destructor in datatype '{1}'", destructor_str, dt.Name);
          } else {
            members.Add(member);
            var destructor = (DatatypeDestructor)member;
            var intersection = new List<DatatypeCtor>(candidateResultCtors.Intersect(destructor.EnclosingCtors));
            if (intersection.Count == 0) {
              reporter.Error(MessageSource.Resolver, entry.Item1,
                "updated datatype members must belong to the same constructor (unlike the previously mentioned destructors, '{0}' does not belong to {1})",
                destructor_str, DatatypeDestructor.PrintableCtorNameList(candidateResultCtors, "or"));
            } else {
              candidateResultCtors = intersection;
              if (destructor.IsGhost) {
                rhsBindings.Add(destructor_str, new Tuple<BoundVar, IdentifierExpr, Expression>(null, null, entry.Item3));
              } else {
                var xName = FreshTempVarName(string.Format("dt_update#{0}#", destructor_str), resolutionContext.CodeContext);
                var xVar = new BoundVar(new AutoGeneratedToken(tok), xName, destructor.Type.Subst(subst));
                var x = new IdentifierExpr(new AutoGeneratedToken(tok), xVar);
                rhsBindings.Add(destructor_str, new Tuple<BoundVar, IdentifierExpr, Expression>(xVar, x, entry.Item3));
              }
            }
          }
        }
      }
      if (candidateResultCtors.Count == 0) {
        return (null, null);
      }

      // Check that every candidate result constructor has given a name to all of its parameters.
      var hasError = false;
      foreach (var ctor in candidateResultCtors) {
        if (ctor.Formals.Exists(f => !f.HasName)) {
          reporter.Error(MessageSource.Resolver, tok,
            "candidate result constructor '{0}' has an anonymous parameter (to use in datatype update expression, name all the parameters of the candidate result constructors)",
            ctor.Name);
          hasError = true;
        }
      }
      if (hasError) {
        return (null, null);
      }

      // The legal source constructors are the candidate result constructors. (Yep, two names for the same thing.)
      legalSourceConstructors = candidateResultCtors;
      Contract.Assert(1 <= legalSourceConstructors.Count);

      var desugaringForGhostContext = DesugarDatatypeUpdate(tok, root, dt, candidateResultCtors, rhsBindings, resolutionContext);
      var nonGhostConstructors = candidateResultCtors.Where(ctor => !ctor.IsGhost).ToList();
      if (nonGhostConstructors.Count == candidateResultCtors.Count) {
        return (desugaringForGhostContext, desugaringForGhostContext);
      }
      var desugaringForCompiledContext = DesugarDatatypeUpdate(tok, root, dt, nonGhostConstructors, rhsBindings, resolutionContext);
      return (desugaringForGhostContext, desugaringForCompiledContext);
    }

    /// <summary>
    // Rewrite the datatype update root.(x := X, y := Y, ...) to:
    ///     var d := root;
    ///     var x := X;  // EXCEPT: don't do this for ghost fields
    ///     var y := Y;
    ///     ..
    ///     if d.CandidateResultConstructor0 then
    ///       CandidateResultConstructor0(x, y, ..., d.f0, d.f1, ...)  // for a ghost field x, use the expression X directly
    ///     else if d.CandidateResultConstructor1 then
    ///       CandidateResultConstructor0(x, y, ..., d.g0, d.g1, ...)
    ///     ...
    ///     else
    ///       CandidateResultConstructorN(x, y, ..., d.k0, d.k1, ...)
    /// </summary>
    private Expression DesugarDatatypeUpdate(IToken tok, Expression root, DatatypeDecl dt, List<DatatypeCtor> candidateResultCtors,
      Dictionary<string, Tuple<BoundVar, IdentifierExpr, Expression>> rhsBindings, ResolutionContext resolutionContext) {

      if (candidateResultCtors.Count == 0) {
        return root;
      }
      Expression rewrite = null;
      // Create a unique name for d', the variable we introduce in the let expression
      var dName = FreshTempVarName("dt_update_tmp#", resolutionContext.CodeContext);
      var dVar = new BoundVar(new AutoGeneratedToken(tok), dName, root.Type);
      var d = new IdentifierExpr(new AutoGeneratedToken(tok), dVar);
      Expression body = null;
      candidateResultCtors.Reverse();
      foreach (var crc in candidateResultCtors) {
        // Build the arguments to the datatype constructor, using the updated value in the appropriate slot
        var ctorArguments = new List<Expression>();
        var actualBindings = new List<ActualBinding>();
        foreach (var f in crc.Formals) {
          Expression ctorArg;
          if (rhsBindings.TryGetValue(f.Name, out var info)) {
            ctorArg = info.Item2 ?? info.Item3;
          } else {
            ctorArg = new ExprDotName(tok, d, f.Name, null);
          }
          ctorArguments.Add(ctorArg);
          var bindingName = new Token(tok.line, tok.col) {
            Filename = tok.Filename,
            val = f.Name
          };
          actualBindings.Add(new ActualBinding(bindingName, ctorArg));
        }
        var ctor_call = new DatatypeValue(tok, crc.EnclosingDatatype.Name, crc.Name, actualBindings);
        // in the following line, resolve to root.Type, so that type parameters get filled in appropriately
        ResolveDatatypeValue(resolutionContext, ctor_call, dt, root.Type.NormalizeExpand());

        if (body == null) {
          body = ctor_call;
        } else {
          // body = if d.crc? then ctor_call else body
          var guard = new ExprDotName(tok, d, crc.QueryField.Name, null);
          body = new ITEExpr(tok, false, guard, ctor_call, body);
        }
      }
      Contract.Assert(body != null); // because there was at least one element in candidateResultCtors

      // Wrap the let's around body
      rewrite = body;
      foreach (var entry in rhsBindings) {
        if (entry.Value.Item1 != null) {
          var lhs = new CasePattern<BoundVar>(tok, entry.Value.Item1);
          rewrite = new LetExpr(tok, new List<CasePattern<BoundVar>>() { lhs }, new List<Expression>() { entry.Value.Item3 }, rewrite, true);
        }
      }
      var dVarPat = new CasePattern<BoundVar>(tok, dVar);
      rewrite = new LetExpr(tok, new List<CasePattern<BoundVar>>() { dVarPat }, new List<Expression>() { root }, rewrite, true);
      Contract.Assert(rewrite != null);
      ResolveExpression(rewrite, resolutionContext);
      return rewrite;
    }

    public Expression ResolveNameSegment(NameSegment expr, bool isLastNameSegment, List<ActualBinding> args,
      ResolutionContext resolutionContext, bool allowMethodCall, bool complain = true) {
      return ResolveNameSegment(expr, isLastNameSegment, args, resolutionContext, allowMethodCall, complain, out _);
    }

    /// <summary>
    /// Look up expr.Name in the following order:
    ///  0. Local variable, parameter, or bound variable.
    ///     (Language design note:  If this clashes with something of interest, one can always rename the local variable locally.)
    ///  1. Member of enclosing class (an implicit "this" is inserted, if needed)
    ///  2. If isLastNameSegment:
    ///     Unambiguous constructor name of a datatype in the enclosing module (if two constructors have the same name, an error message is produced here)
    ///     (Language design note:  If the constructor name is ambiguous or if one of the steps above takes priority, one can qualify the constructor name with the name of the datatype)
    ///  3. Member of the enclosing module (type name or the name of a module)
    ///  4. Static function or method in the enclosing module or its imports
    ///  5. If !isLastNameSegment:
    ///     Unambiguous constructor name of a datatype in the enclosing module
    ///
    /// </summary>
    /// <param name="expr"></param>
    /// <param name="isLastNameSegment">Indicates that the NameSegment is not directly enclosed in another NameSegment or ExprDotName expression.</param>
    /// <param name="args">If the NameSegment is enclosed in an ApplySuffix, then these are the arguments.  The method returns null to indicate
    /// that these arguments, if any, were not used.  If args is non-null and the method does use them, the method returns the resolved expression
    /// that incorporates these arguments.</param>
    /// <param name="resolutionContext"></param>
    /// <param name="allowMethodCall">If false, generates an error if the name denotes a method. If true and the name denotes a method, returns
    /// a MemberSelectExpr whose .Member is a Method.</param>
    /// <param name="shadowedModule">If the name being resolved shadows an imported module, then that module is reported
    /// through this parameter.  This happens when module <c>Option</c> in <c>import opened Option</c> also contains a
    /// <c>datatype Option</c>, in which case <c>Option</c> refers to the datatype, not the module
    /// (https://github.com/dafny-lang/dafny/issues/1996).</param>
    Expression ResolveNameSegment(NameSegment expr, bool isLastNameSegment, List<ActualBinding> args, ResolutionContext resolutionContext, bool allowMethodCall, bool complain, out ModuleDecl shadowedModule) {
      Contract.Requires(expr != null);
      Contract.Requires(!expr.WasResolved());
      Contract.Requires(resolutionContext != null);
      Contract.Ensures(Contract.Result<Expression>() == null || args != null);

      shadowedModule = null;

      if (expr.OptTypeArguments != null) {
        foreach (var ty in expr.OptTypeArguments) {
          ResolveType(expr.tok, ty, resolutionContext, ResolveTypeOptionEnum.InferTypeProxies, null);
        }
      }

      Expression r = null;  // the resolved expression, if successful
      Expression rWithArgs = null;  // the resolved expression after incorporating "args"

      // For 0:
      IVariable v;
      // For 1:
      Dictionary<string, MemberDecl> members;
      // For 1 and 4:
      MemberDecl member = null;
      // For 2 and 5:
      Tuple<DatatypeCtor, bool> pair;
      // For 3:
      TopLevelDecl decl;

      var name = resolutionContext.InReveal ? "reveal_" + expr.Name : expr.Name;
      v = scope.Find(name);
      if (v != null) {
        // ----- 0. local variable, parameter, or bound variable
        if (expr.OptTypeArguments != null) {
          if (complain) {
            reporter.Error(MessageSource.Resolver, expr.tok, "variable '{0}' does not take any type parameters", name);
          } else {
            expr.ResolvedExpression = null;
            return null;
          }
        }
        r = new IdentifierExpr(expr.tok, v);
      } else if (currentClass is TopLevelDeclWithMembers cl && classMembers.TryGetValue(cl, out members) && members.TryGetValue(name, out member)) {
        // ----- 1. member of the enclosing class
        Expression receiver;
        if (member.IsStatic) {
          receiver = new StaticReceiverExpr(expr.tok, UserDefinedType.FromTopLevelDecl(expr.tok, currentClass, currentClass.TypeArgs), (TopLevelDeclWithMembers)member.EnclosingClass, true);
        } else {
          if (!scope.AllowInstance) {
            if (complain) {
              reporter.Error(MessageSource.Resolver, expr.tok, "'this' is not allowed in a 'static' context"); //TODO: Rephrase this
            } else {
              expr.ResolvedExpression = null;
              return null;
            }
            // nevertheless, set "receiver" to a value so we can continue resolution
          }
          receiver = new ImplicitThisExpr(expr.tok);
          receiver.Type = GetThisType(expr.tok, currentClass);  // resolve here
        }
        r = ResolveExprDotCall(expr.tok, receiver, null, member, args, expr.OptTypeArguments, resolutionContext, allowMethodCall);
      } else if (isLastNameSegment && moduleInfo.Ctors.TryGetValue(name, out pair)) {
        // ----- 2. datatype constructor
        if (ResolveDatatypeConstructor(expr, args, resolutionContext, complain, pair, name, ref r, ref rWithArgs)) {
          return null;
        }
      } else if (moduleInfo.TopLevels.TryGetValue(name, out decl)) {
        // ----- 3. Member of the enclosing module

        // Record which imported module, if any, was shadowed by `name` in the current module.
        shadowedModule = moduleInfo.ShadowedImportedModules.GetValueOrDefault(name);

        if (decl is AmbiguousTopLevelDecl) {
          var ad = (AmbiguousTopLevelDecl)decl;
          if (complain) {
            reporter.Error(MessageSource.Resolver, expr.tok, "The name {0} ambiguously refers to a type in one of the modules {1} (try qualifying the type name with the module name)", expr.Name, ad.ModuleNames());
          } else {
            expr.ResolvedExpression = null;
            return null;
          }
        } else {
          // We have found a module name or a type name, neither of which is an expression. However, the NameSegment we're
          // looking at may be followed by a further suffix that makes this into an expresion. We postpone the rest of the
          // resolution to any such suffix. For now, we create a temporary expression that will never be seen by the compiler
          // or verifier, just to have a placeholder where we can recorded what we have found.
          if (!isLastNameSegment) {
            if (decl is ClassDecl cd && cd.NonNullTypeDecl != null && name != cd.NonNullTypeDecl.Name) {
              // A possibly-null type C? was mentioned. But it does not have any further members. The program should have used
              // the name of the class, C. Report an error and continue.
              if (complain) {
                reporter.Error(MessageSource.Resolver, expr.tok, "To access members of {0} '{1}', write '{1}', not '{2}'", decl.WhatKind, decl.Name, name);
              } else {
                expr.ResolvedExpression = null;
                return null;
              }
            }
          }
          r = CreateResolver_IdentifierExpr(expr.tok, name, expr.OptTypeArguments, decl);
        }

      } else if (moduleInfo.StaticMembers.TryGetValue(name, out member)) {
        // ----- 4. static member of the enclosing module
        Contract.Assert(member.IsStatic); // moduleInfo.StaticMembers is supposed to contain only static members of the module's implicit class _default
        if (member is AmbiguousMemberDecl) {
          var ambiguousMember = (AmbiguousMemberDecl)member;
          if (complain) {
            reporter.Error(MessageSource.Resolver, expr.tok, "The name {0} ambiguously refers to a static member in one of the modules {1} (try qualifying the member name with the module name)", expr.Name, ambiguousMember.ModuleNames());
          } else {
            expr.ResolvedExpression = null;
            return null;
          }
        } else {
          var receiver = new StaticReceiverExpr(expr.tok, (ClassDecl)member.EnclosingClass, true);
          r = ResolveExprDotCall(expr.tok, receiver, null, member, args, expr.OptTypeArguments, resolutionContext, allowMethodCall);
        }

      } else if (!isLastNameSegment && moduleInfo.Ctors.TryGetValue(name, out pair)) {
        // ----- 5. datatype constructor
        if (ResolveDatatypeConstructor(expr, args, resolutionContext, complain, pair, name, ref r, ref rWithArgs)) {
          return null;
        }

      } else {
        // ----- None of the above
        if (complain) {
          reporter.Error(MessageSource.Resolver, expr.tok, "unresolved identifier: {0}", name);
        } else {
          expr.ResolvedExpression = null;
          return null;
        }
      }

      if (r == null) {
        // an error has been reported above; we won't fill in .ResolvedExpression, but we still must fill in .Type
        expr.Type = new InferredTypeProxy();
      } else {
        expr.ResolvedExpression = r;
        var rt = r.Type;
        var nt = rt.UseInternalSynonym();
        expr.Type = nt;
      }
      return rWithArgs;
    }

    private bool ResolveDatatypeConstructor(NameSegment expr, List<ActualBinding>/*?*/ args, ResolutionContext resolutionContext, bool complain, Tuple<DatatypeCtor, bool> pair, string name, ref Expression r, ref Expression rWithArgs) {
      Contract.Requires(expr != null);
      Contract.Requires(resolutionContext != null);

      if (pair.Item2) {
        // there is more than one constructor with this name
        if (complain) {
          reporter.Error(MessageSource.Resolver, expr.tok, "the name '{0}' denotes a datatype constructor, but does not do so uniquely; add an explicit qualification (for example, '{1}.{0}')", expr.Name,
            pair.Item1.EnclosingDatatype.Name);
        } else {
          expr.ResolvedExpression = null;
          return true;
        }
      } else {
        if (expr.OptTypeArguments != null) {
          if (complain) {
            reporter.Error(MessageSource.Resolver, expr.tok, "datatype constructor does not take any type parameters ('{0}')", name);
          } else {
            expr.ResolvedExpression = null;
            return true;
          }
        }
        var rr = new DatatypeValue(expr.tok, pair.Item1.EnclosingDatatype.Name, name, args ?? new List<ActualBinding>());
        bool ok = ResolveDatatypeValue(resolutionContext, rr, pair.Item1.EnclosingDatatype, null, complain);
        if (!ok) {
          expr.ResolvedExpression = null;
          return true;
        }
        if (args == null) {
          r = rr;
        } else {
          r = rr; // this doesn't really matter, since we're returning an "rWithArgs" (but if would have been proper to have returned the ctor as a lambda)
          rWithArgs = rr;
        }
      }
      return false;
    }

    /// <summary>
    /// Look up expr.Name in the following order:
    ///  0. Type parameter
    ///  1. Member of enclosing class (an implicit "this" is inserted, if needed)
    ///  2. Member of the enclosing module (type name or the name of a module)
    ///  3. Static function or method in the enclosing module or its imports
    ///
    /// Note: 1 and 3 are not used now, but they will be of interest when async task types are supported.
    /// </summary>
    void ResolveNameSegment_Type(NameSegment expr, ResolutionContext resolutionContext, ResolveTypeOption option, List<TypeParameter> defaultTypeArguments) {
      Contract.Requires(expr != null);
      Contract.Requires(!expr.WasResolved());
      Contract.Requires(resolutionContext != null);
      Contract.Requires((option.Opt == ResolveTypeOptionEnum.DontInfer || option.Opt == ResolveTypeOptionEnum.InferTypeProxies) == (defaultTypeArguments == null));

      if (expr.OptTypeArguments != null) {
        foreach (var ty in expr.OptTypeArguments) {
          ResolveType(expr.tok, ty, resolutionContext, option, defaultTypeArguments);
        }
      }

      Expression r = null;  // the resolved expression, if successful

      // For 0:
      TypeParameter tp;
#if ASYNC_TASK_TYPES
      // For 1:
      Dictionary<string, MemberDecl> members;
      // For 1 and 3:
      MemberDecl member = null;
#endif
      // For 2:
      TopLevelDecl decl;

      tp = allTypeParameters.Find(expr.Name);
      if (tp != null) {
        // ----- 0. type parameter
        if (expr.OptTypeArguments == null) {
          r = new Resolver_IdentifierExpr(expr.tok, tp);
        } else {
          reporter.Error(MessageSource.Resolver, expr.tok, "Type parameter expects no type arguments: {0}", expr.Name);
        }
#if ASYNC_TASK_TYPES  // At the moment, there is no way for a class member to part of a type name, but this changes with async task types
      } else if (currentClass != null && classMembers.TryGetValue(currentClass, out members) && members.TryGetValue(expr.Name, out member)) {
        // ----- 1. member of the enclosing class
        Expression receiver;
        if (member.IsStatic) {
          receiver = new StaticReceiverExpr(expr.tok, (ClassDecl)member.EnclosingClass);
        } else {
          if (!scope.AllowInstance) {
            reporter.Error(MessageSource.Resolver, expr.tok, "'this' is not allowed in a 'static' context");
            // nevertheless, set "receiver" to a value so we can continue resolution
          }
          receiver = new ImplicitThisExpr(expr.tok);
          receiver.Type = GetThisType(expr.tok, (ClassDecl)member.EnclosingClass);  // resolve here
        }
        r = ResolveExprDotCall(expr.tok, receiver, member, expr.OptTypeArguments, opts.resolutionContext, allowMethodCall);
#endif
      } else if (moduleInfo.TopLevels.TryGetValue(expr.Name, out decl)) {
        // ----- 2. Member of the enclosing module
        if (decl is AmbiguousTopLevelDecl) {
          var ad = (AmbiguousTopLevelDecl)decl;
          reporter.Error(MessageSource.Resolver, expr.tok, "The name {0} ambiguously refers to a type in one of the modules {1} (try qualifying the type name with the module name)", expr.Name, ad.ModuleNames());
        } else {
          // We have found a module name or a type name, neither of which is a type expression. However, the NameSegment we're
          // looking at may be followed by a further suffix that makes this into a type expresion. We postpone the rest of the
          // resolution to any such suffix. For now, we create a temporary expression that will never be seen by the compiler
          // or verifier, just to have a placeholder where we can recorded what we have found.
          r = CreateResolver_IdentifierExpr(expr.tok, expr.Name, expr.OptTypeArguments, decl);
        }

#if ASYNC_TASK_TYPES  // At the moment, there is no way for a class member to part of a type name, but this changes with async task types
      } else if (moduleInfo.StaticMembers.TryGetValue(expr.Name, out member)) {
        // ----- 3. static member of the enclosing module
        Contract.Assert(member.IsStatic); // moduleInfo.StaticMembers is supposed to contain only static members of the module's implicit class _default
        if (ReallyAmbiguousThing(ref member)) {
          reporter.Error(MessageSource.Resolver, expr.tok, "The name {0} ambiguously refers to a static member in one of the modules {1} (try qualifying the member name with the module name)", expr.Name, ((AmbiguousMemberDecl)member).ModuleNames());
        } else {
          var receiver = new StaticReceiverExpr(expr.tok, (ClassDecl)member.EnclosingClass);
          r = ResolveExprDotCall(expr.tok, receiver, member, expr.OptTypeArguments, opts.resolutionContext, allowMethodCall);
        }
#endif
      } else {
        // ----- None of the above
        reporter.Error(MessageSource.Resolver, expr.tok, "Type or type parameter is not declared in this scope: {0} (did you forget to qualify a name or declare a module import 'opened'? names in outer modules are not visible in nested modules)", expr.Name);
      }

      if (r == null) {
        // an error has been reported above; we won't fill in .ResolvedExpression, but we still must fill in .Type
        expr.Type = new InferredTypeProxy();
      } else {
        expr.ResolvedExpression = r;
        expr.Type = r.Type;
      }
    }

    /// <summary>
    /// To resolve "id" in expression "E . id", do:
    ///  * If E denotes a module name M:
    ///      0. If isLastNameSegment:
    ///         Unambiguous constructor name of a datatype in module M (if two constructors have the same name, an error message is produced here)
    ///         (Language design note:  If the constructor name is ambiguous or if one of the steps above takes priority, one can qualify the constructor name with the name of the datatype)
    ///      1. Member of module M:  sub-module (including submodules of imports), class, datatype, etc.
    ///         (if two imported types have the same name, an error message is produced here)
    ///      2. Static function or method of M._default
    ///    (Note that in contrast to ResolveNameSegment, imported modules, etc. are ignored)
    ///  * If E denotes a type:
    ///      3. Look up id as a member of that type
    ///  * If E denotes an expression:
    ///      4. Let T be the type of E.  Look up id in T.
    /// </summary>
    /// <param name="expr"></param>
    /// <param name="isLastNameSegment">Indicates that the ExprDotName is not directly enclosed in another ExprDotName expression.</param>
    /// <param name="args">If the ExprDotName is enclosed in an ApplySuffix, then these are the arguments.  The method returns null to indicate
    /// that these arguments, if any, were not used.  If args is non-null and the method does use them, the method returns the resolved expression
    /// that incorporates these arguments.</param>
    /// <param name="resolutionContext"></param>
    /// <param name="allowMethodCall">If false, generates an error if the name denotes a method. If true and the name denotes a method, returns
    /// a Resolver_MethodCall.</param>
    Expression ResolveDotSuffix(ExprDotName expr, bool isLastNameSegment, List<ActualBinding> args, ResolutionContext resolutionContext, bool allowMethodCall) {
      Contract.Requires(expr != null);
      Contract.Requires(!expr.WasResolved());
      Contract.Requires(resolutionContext != null);
      Contract.Ensures(Contract.Result<Expression>() == null || args != null);

      // resolve the LHS expression
      // LHS should not be reveal lemma
      ModuleDecl shadowedImport = null;
      ResolutionContext nonRevealOpts = resolutionContext with { InReveal = false };
      if (expr.Lhs is NameSegment) {
        ResolveNameSegment((NameSegment)expr.Lhs, false, null, nonRevealOpts, false, true, out shadowedImport);
      } else if (expr.Lhs is ExprDotName) {
        ResolveDotSuffix((ExprDotName)expr.Lhs, false, null, nonRevealOpts, false);
      } else {
        ResolveExpression(expr.Lhs, nonRevealOpts);
      }

      if (expr.OptTypeArguments != null) {
        foreach (var ty in expr.OptTypeArguments) {
          ResolveType(expr.tok, ty, resolutionContext, ResolveTypeOptionEnum.InferTypeProxies, null);
        }
      }

      Expression r = null;  // the resolved expression, if successful
      Expression rWithArgs = null;  // the resolved expression after incorporating "args"
      MemberDecl member = null;

      var name = resolutionContext.InReveal ? "reveal_" + expr.SuffixName : expr.SuffixName;
      if (!expr.Lhs.WasResolved()) {
        return null;
      }
      var lhs = expr.Lhs.Resolved;
      if (lhs != null && lhs.Type is Resolver_IdentifierExpr.ResolverType_Module) {
        var ri = (Resolver_IdentifierExpr)lhs;
        var sig = ((ModuleDecl)ri.Decl).AccessibleSignature(useCompileSignatures);
        sig = GetSignature(sig);
        // For 0:
        Tuple<DatatypeCtor, bool> pair;
        // For 1:
        TopLevelDecl decl;

        if (isLastNameSegment && sig.Ctors.TryGetValue(name, out pair)) {
          // ----- 0. datatype constructor
          if (pair.Item2) {
            // there is more than one constructor with this name
            reporter.Error(MessageSource.Resolver, expr.tok, "the name '{0}' denotes a datatype constructor in module {2}, but does not do so uniquely; add an explicit qualification (for example, '{1}.{0}')", name, pair.Item1.EnclosingDatatype.Name, ((ModuleDecl)ri.Decl).Name);
          } else {
            if (expr.OptTypeArguments != null) {
              reporter.Error(MessageSource.Resolver, expr.tok, "datatype constructor does not take any type parameters ('{0}')", name);
            }
            var rr = new DatatypeValue(expr.tok, pair.Item1.EnclosingDatatype.Name, name, args ?? new List<ActualBinding>());
            ResolveDatatypeValue(resolutionContext, rr, pair.Item1.EnclosingDatatype, null);

            if (args == null) {
              r = rr;
            } else {
              r = rr;  // this doesn't really matter, since we're returning an "rWithArgs" (but if would have been proper to have returned the ctor as a lambda)
              rWithArgs = rr;
            }
          }
        } else if (sig.TopLevels.TryGetValue(name, out decl)) {
          // ----- 1. Member of the specified module
          if (decl is AmbiguousTopLevelDecl) {
            var ad = (AmbiguousTopLevelDecl)decl;
            reporter.Error(MessageSource.Resolver, expr.tok, "The name {0} ambiguously refers to a type in one of the modules {1} (try qualifying the type name with the module name)", expr.SuffixName, ad.ModuleNames());
          } else {
            // We have found a module name or a type name, neither of which is an expression. However, the ExprDotName we're
            // looking at may be followed by a further suffix that makes this into an expresion. We postpone the rest of the
            // resolution to any such suffix. For now, we create a temporary expression that will never be seen by the compiler
            // or verifier, just to have a placeholder where we can recorded what we have found.
            if (!isLastNameSegment) {
              if (decl is ClassDecl cd && cd.NonNullTypeDecl != null && name != cd.NonNullTypeDecl.Name) {
                // A possibly-null type C? was mentioned. But it does not have any further members. The program should have used
                // the name of the class, C. Report an error and continue.
                reporter.Error(MessageSource.Resolver, expr.tok, "To access members of {0} '{1}', write '{1}', not '{2}'", decl.WhatKind, decl.Name, name);
              }
            }
            r = CreateResolver_IdentifierExpr(expr.tok, name, expr.OptTypeArguments, decl);
          }
        } else if (sig.StaticMembers.TryGetValue(name, out member)) {
          // ----- 2. static member of the specified module
          Contract.Assert(member.IsStatic); // moduleInfo.StaticMembers is supposed to contain only static members of the module's implicit class _default
          if (member is AmbiguousMemberDecl) {
            var ambiguousMember = (AmbiguousMemberDecl)member;
            reporter.Error(MessageSource.Resolver, expr.tok, "The name {0} ambiguously refers to a static member in one of the modules {1} (try qualifying the member name with the module name)", expr.SuffixName, ambiguousMember.ModuleNames());
          } else {
            var receiver = new StaticReceiverExpr(expr.Lhs.tok, (ClassDecl)member.EnclosingClass, false);
            receiver.ContainerExpression = expr.Lhs;
            r = ResolveExprDotCall(expr.tok, receiver, null, member, args, expr.OptTypeArguments, resolutionContext, allowMethodCall);
          }
        } else {
          reporter.Error(MessageSource.Resolver, expr.tok, "unresolved identifier: {0}", name);
        }

      } else if (lhs != null && lhs.Type is Resolver_IdentifierExpr.ResolverType_Type) {
        var ri = (Resolver_IdentifierExpr)lhs;
        // ----- 3. Look up name in type
        // expand any synonyms
        var ty = new UserDefinedType(expr.tok, ri.Decl.Name, ri.Decl, ri.TypeArgs).NormalizeExpand();
        if (ty.IsDatatype) {
          // ----- LHS is a datatype
          var dt = ty.AsDatatype;
          DatatypeCtor ctor;
          if (dt.ConstructorsByName != null && dt.ConstructorsByName.TryGetValue(name, out ctor)) {
            if (expr.OptTypeArguments != null) {
              reporter.Error(MessageSource.Resolver, expr.tok, "datatype constructor does not take any type parameters ('{0}')", name);
            }
            var rr = new DatatypeValue(expr.tok, ctor.EnclosingDatatype.Name, name, args ?? new List<ActualBinding>());
            ResolveDatatypeValue(resolutionContext, rr, ctor.EnclosingDatatype, ty);
            if (args == null) {
              r = rr;
            } else {
              r = rr;  // this doesn't really matter, since we're returning an "rWithArgs" (but if would have been proper to have returned the ctor as a lambda)
              rWithArgs = rr;
            }
          }
        }
        var cd = r == null ? ty.AsTopLevelTypeWithMembersBypassInternalSynonym : null;
        if (cd != null) {
          // ----- LHS is a type with members
          Dictionary<string, MemberDecl> members;
          if (classMembers.TryGetValue(cd, out members) && members.TryGetValue(name, out member)) {
            if (!VisibleInScope(member)) {
              reporter.Error(MessageSource.Resolver, expr.tok, "member '{0}' has not been imported in this scope and cannot be accessed here", name);
            }
            if (!member.IsStatic) {
              reporter.Error(MessageSource.Resolver, expr.tok, "accessing member '{0}' requires an instance expression", name); //TODO Unify with similar error messages
              // nevertheless, continue creating an expression that approximates a correct one
            }
            var receiver = new StaticReceiverExpr(expr.Lhs.tok, (UserDefinedType)ty.NormalizeExpand(), (TopLevelDeclWithMembers)member.EnclosingClass, false);
            receiver.ContainerExpression = expr.Lhs;
            r = ResolveExprDotCall(expr.tok, receiver, null, member, args, expr.OptTypeArguments, resolutionContext, allowMethodCall);
          }
        }
        if (r == null) {
          reporter.Error(MessageSource.Resolver, expr.tok, "member '{0}' does not exist in {2} '{1}'", name, ri.Decl.Name, ri.Decl.WhatKind);
        }
      } else if (lhs != null) {
        // ----- 4. Look up name in the type of the Lhs
        NonProxyType tentativeReceiverType;
        member = ResolveMember(expr.tok, expr.Lhs.Type, name, out tentativeReceiverType);
        if (member != null) {
          Expression receiver;
          if (!member.IsStatic) {
            receiver = expr.Lhs;
            AddAssignableConstraint(expr.tok, tentativeReceiverType, receiver.Type, "receiver type ({1}) does not have a member named " + name);
            r = ResolveExprDotCall(expr.tok, receiver, tentativeReceiverType, member, args, expr.OptTypeArguments, resolutionContext, allowMethodCall);
          } else {
            receiver = new StaticReceiverExpr(expr.tok, (UserDefinedType)tentativeReceiverType, (TopLevelDeclWithMembers)member.EnclosingClass, false, lhs);
            r = ResolveExprDotCall(expr.tok, receiver, null, member, args, expr.OptTypeArguments, resolutionContext, allowMethodCall);
          }
        }
      }

      if (r == null) {
        // an error has been reported above; we won't fill in .ResolvedExpression, but we still must fill in .Type
        expr.Type = new InferredTypeProxy();
      } else {
        CheckForAmbiguityInShadowedImportedModule(shadowedImport, name, expr.tok, useCompileSignatures, isLastNameSegment);
        expr.ResolvedExpression = r;
        expr.Type = r.Type;
      }
      return rWithArgs;
    }

    /// <summary>
    /// Check whether the name we just resolved may have been resolved differently if we didn't allow member `M.M` of
    /// module `M` to shadow `M` when the user writes `import opened M`.  Raising an error in that case allowed us to
    /// change the behavior of `import opened` without silently changing the meaning of existing programs.
    /// (https://github.com/dafny-lang/dafny/issues/1996)
    ///
    /// Note the extra care for the constructor case, which is needed because the constructors of datatype `M.M` are
    /// exposed through both `M` and `M.M`, without ambiguity.
    /// </summary>
    private void CheckForAmbiguityInShadowedImportedModule(ModuleDecl moduleDecl, string name,
      IToken tok, bool useCompileSignatures, bool isLastNameSegment) {
      if (moduleDecl != null && NameConflictsWithModuleContents(moduleDecl, name, useCompileSignatures, isLastNameSegment)) {
        reporter.Error(MessageSource.Resolver, tok,
          "Reference to member '{0}' is ambiguous: name '{1}' shadows an import-opened module of the same name, and "
          + "both have a member '{0}'. To solve this issue, give a different name to the imported module using "
          + "`import opened XYZ = ...` instead of `import opened ...`.",
          name, moduleDecl.Name);
      }
    }

    private bool NameConflictsWithModuleContents(ModuleDecl moduleDecl, string name, bool useCompileSignatures, bool isLastNameSegment) {
      var sig = GetSignature(moduleDecl.AccessibleSignature(useCompileSignatures));
      return (
        (isLastNameSegment
         && sig.Ctors.GetValueOrDefault(name) is { Item1: var constructor, Item2: var ambiguous }
         && !ambiguous && constructor.EnclosingDatatype.Name != moduleDecl.Name)
        || sig.TopLevels.ContainsKey(name)
        || sig.StaticMembers.ContainsKey(name)
      );
    }

    Expression ResolveExprDotCall(IToken tok, Expression receiver, Type receiverTypeBound/*?*/,
      MemberDecl member, List<ActualBinding> args, List<Type> optTypeArguments, ResolutionContext resolutionContext, bool allowMethodCall) {
      Contract.Requires(tok != null);
      Contract.Requires(receiver != null);
      Contract.Requires(receiver.WasResolved());
      Contract.Requires(member != null);
      Contract.Requires(resolutionContext != null && resolutionContext.CodeContext != null);

      var rr = new MemberSelectExpr(tok, receiver, member.Name);
      rr.Member = member;

      // Now, fill in rr.Type.  This requires taking into consideration the type parameters passed to the receiver's type as well as any type
      // parameters used in this NameSegment/ExprDotName.
      // Add to "subst" the type parameters given to the member's class/datatype
      rr.TypeApplication_AtEnclosingClass = new List<Type>();
      rr.TypeApplication_JustMember = new List<Type>();
      Dictionary<TypeParameter, Type> subst;
      var rType = (receiverTypeBound ?? receiver.Type).NormalizeExpand();
      if (rType is UserDefinedType udt && udt.ResolvedClass != null) {
        subst = TypeParameter.SubstitutionMap(udt.ResolvedClass.TypeArgs, udt.TypeArgs);
        if (member.EnclosingClass == null) {
          // this can happen for some special members, like real.Floor
        } else {
          rr.TypeApplication_AtEnclosingClass.AddRange(rType.AsParentType(member.EnclosingClass).TypeArgs);
        }
      } else {
        var vtd = AsValuetypeDecl(rType);
        if (vtd != null) {
          Contract.Assert(vtd.TypeArgs.Count == rType.TypeArgs.Count);
          subst = TypeParameter.SubstitutionMap(vtd.TypeArgs, rType.TypeArgs);
          rr.TypeApplication_AtEnclosingClass.AddRange(rType.TypeArgs);
        } else {
          Contract.Assert(rType.TypeArgs.Count == 0);
          subst = new Dictionary<TypeParameter, Type>();
        }
      }

      if (member is Field) {
        var field = (Field)member;
        if (optTypeArguments != null) {
          reporter.Error(MessageSource.Resolver, tok, "a field ({0}) does not take any type arguments (got {1})", field.Name, optTypeArguments.Count);
        }
        subst = BuildTypeArgumentSubstitute(subst, receiverTypeBound ?? receiver.Type);
        rr.Type = field.Type.Subst(subst);
      } else if (member is Function) {
        var fn = (Function)member;
        if (fn is TwoStateFunction && !resolutionContext.IsTwoState) {
          reporter.Error(MessageSource.Resolver, tok, "two-state function ('{0}') can only be called in a two-state context", member.Name);
        }
        int suppliedTypeArguments = optTypeArguments == null ? 0 : optTypeArguments.Count;
        if (optTypeArguments != null && suppliedTypeArguments != fn.TypeArgs.Count) {
          reporter.Error(MessageSource.Resolver, tok, "function '{0}' expects {1} type argument{2} (got {3})",
            member.Name, fn.TypeArgs.Count, Util.Plural(fn.TypeArgs.Count), suppliedTypeArguments);
        }
        for (int i = 0; i < fn.TypeArgs.Count; i++) {
          var ta = i < suppliedTypeArguments ? optTypeArguments[i] : new InferredTypeProxy();
          rr.TypeApplication_JustMember.Add(ta);
          subst.Add(fn.TypeArgs[i], ta);
        }
        subst = BuildTypeArgumentSubstitute(subst, receiverTypeBound ?? receiver.Type);
        rr.Type = SelectAppropriateArrowType(fn.tok,
          fn.Formals.ConvertAll(f => f.Type.Subst(subst)),
          fn.ResultType.Subst(subst),
          fn.Reads.Count != 0, fn.Req.Count != 0);
      } else {
        // the member is a method
        var m = (Method)member;
        if (!allowMethodCall) {
          // it's a method and method calls are not allowed in the given context
          reporter.Error(MessageSource.Resolver, tok, "expression is not allowed to invoke a {0} ({1})", member.WhatKind, member.Name);
        }
        int suppliedTypeArguments = optTypeArguments == null ? 0 : optTypeArguments.Count;
        if (optTypeArguments != null && suppliedTypeArguments != m.TypeArgs.Count) {
          reporter.Error(MessageSource.Resolver, tok, "method '{0}' expects {1} type argument{2} (got {3})",
            member.Name, m.TypeArgs.Count, Util.Plural(m.TypeArgs.Count), suppliedTypeArguments);
        }
        for (int i = 0; i < m.TypeArgs.Count; i++) {
          var ta = i < suppliedTypeArguments ? optTypeArguments[i] : new InferredTypeProxy();
          rr.TypeApplication_JustMember.Add(ta);
          subst.Add(m.TypeArgs[i], ta);
        }
        subst = BuildTypeArgumentSubstitute(subst, receiverTypeBound ?? receiver.Type);
        rr.ResolvedOutparameterTypes = m.Outs.ConvertAll(f => f.Type.Subst(subst));
        rr.Type = new InferredTypeProxy();  // fill in this field, in order to make "rr" resolved
      }
      return rr;
    }

    public MethodCallInformation ResolveApplySuffix(ApplySuffix e, ResolutionContext resolutionContext, bool allowMethodCall) {
      Contract.Requires(e != null);
      Contract.Requires(resolutionContext != null);
      Contract.Ensures(Contract.Result<MethodCallInformation>() == null || allowMethodCall);
      Expression r = null;  // upon success, the expression to which the ApplySuffix resolves
      var errorCount = reporter.Count(ErrorLevel.Error);
      if (e.Lhs is NameSegment) {
        r = ResolveNameSegment((NameSegment)e.Lhs, true, e.Bindings.ArgumentBindings, resolutionContext, allowMethodCall);
        // note, if r is non-null, then e.Args have been resolved and r is a resolved expression that incorporates e.Args
      } else if (e.Lhs is ExprDotName) {
        r = ResolveDotSuffix((ExprDotName)e.Lhs, true, e.Bindings.ArgumentBindings, resolutionContext, allowMethodCall);
        // note, if r is non-null, then e.Args have been resolved and r is a resolved expression that incorporates e.Args
      } else {
        ResolveExpression(e.Lhs, resolutionContext);
      }
      if (e.Lhs.Type == null) {
        // some error had been detected during the attempted resolution of e.Lhs
        e.Lhs.Type = new InferredTypeProxy();
      }
      Label atLabel = null;
      if (e.AtTok != null) {
        atLabel = DominatingStatementLabels.Find(e.AtTok.val);
        if (atLabel == null) {
          reporter.Error(MessageSource.Resolver, e.AtTok, "no label '{0}' in scope at this time", e.AtTok.val);
        }
      }
      if (r == null) {
        var improvedType = PartiallyResolveTypeForMemberSelection(e.Lhs.tok, e.Lhs.Type, "_#apply");
        var fnType = improvedType.AsArrowType;
        if (fnType == null) {
          var lhs = e.Lhs.Resolved;
          if (lhs != null && lhs.Type is Resolver_IdentifierExpr.ResolverType_Module) {
            reporter.Error(MessageSource.Resolver, e.tok, "name of module ({0}) is used as a function", ((Resolver_IdentifierExpr)lhs).Decl.Name);
          } else if (lhs != null && lhs.Type is Resolver_IdentifierExpr.ResolverType_Type) {
            var ri = (Resolver_IdentifierExpr)lhs;
            reporter.Error(MessageSource.Resolver, e.tok, "name of {0} ({1}) is used as a function", ri.Decl.WhatKind, ri.Decl.Name);
          } else {
            if (lhs is MemberSelectExpr mse && mse.Member is Method) {
              if (atLabel != null) {
                Contract.Assert(mse != null); // assured by the parser
                if (mse.Member is TwoStateLemma) {
                  mse.AtLabel = atLabel;
                } else {
                  reporter.Error(MessageSource.Resolver, e.AtTok, "an @-label can only be applied to a two-state lemma");
                }
              }
              if (allowMethodCall) {
                Contract.Assert(!e.Bindings.WasResolved); // we expect that .Bindings has not yet been processed, so we use just .ArgumentBindings in the next line
                var tok = DafnyOptions.O.Get(DafnyConsolePrinter.ShowSnippets) ? e.RangeToken.ToToken() : e.tok;
                var cRhs = new MethodCallInformation(tok, mse, e.Bindings.ArgumentBindings);
                return cRhs;
              } else {
                reporter.Error(MessageSource.Resolver, e.tok, "{0} call is not allowed to be used in an expression context ({1})", mse.Member.WhatKind, mse.Member.Name);
              }
            } else if (lhs != null) {  // if e.Lhs.Resolved is null, then e.Lhs was not successfully resolved and an error has already been reported
              reporter.Error(MessageSource.Resolver, e.tok, "non-function expression (of type {0}) is called with parameters", e.Lhs.Type);
            }
          }
          // resolve the arguments, even in the presence of the errors above
          foreach (var binding in e.Bindings.ArgumentBindings) {
            ResolveExpression(binding.Actual, resolutionContext);
          }
        } else {
          var mse = e.Lhs is NameSegment || e.Lhs is ExprDotName ? e.Lhs.Resolved as MemberSelectExpr : null;
          var callee = mse == null ? null : mse.Member as Function;
          if (atLabel != null && !(callee is TwoStateFunction)) {
            reporter.Error(MessageSource.Resolver, e.AtTok, "an @-label can only be applied to a two-state function");
            atLabel = null;
          }
          if (callee != null) {
            // produce a FunctionCallExpr instead of an ApplyExpr(MemberSelectExpr)
            var rr = new FunctionCallExpr(e.Lhs.tok, callee.Name, mse.Obj, e.tok, e.CloseParen, e.Bindings, atLabel) {
              Function = callee,
              TypeApplication_AtEnclosingClass = mse.TypeApplication_AtEnclosingClass,
              TypeApplication_JustFunction = mse.TypeApplication_JustMember
            };
            var typeMap = BuildTypeArgumentSubstitute(mse.TypeArgumentSubstitutionsAtMemberDeclaration());
            ResolveActualParameters(rr.Bindings, callee.Formals, e.tok, callee, resolutionContext, typeMap, callee.IsStatic ? null : mse.Obj);
            rr.Type = callee.ResultType.Subst(typeMap);
            if (errorCount == reporter.Count(ErrorLevel.Error)) {
              Contract.Assert(!(mse.Obj is StaticReceiverExpr) || callee.IsStatic);  // this should have been checked already
              Contract.Assert(callee.Formals.Count == rr.Args.Count);  // this should have been checked already
            }
            r = rr;
          } else {
            List<Formal> formals;
            if (callee != null) {
              formals = callee.Formals;
            } else {
              formals = new List<Formal>();
              for (var i = 0; i < fnType.Args.Count; i++) {
                var argType = fnType.Args[i];
                var formal = new ImplicitFormal(e.tok, "_#p" + i, argType, true, false);
                formals.Add(formal);
              }
            }
            ResolveActualParameters(e.Bindings, formals, e.tok, fnType, resolutionContext, new Dictionary<TypeParameter, Type>(), null);
            r = new ApplyExpr(e.Lhs.tok, e.Lhs, e.Args, e.CloseParen);
            r.Type = fnType.Result;
          }
        }
      }
      if (r == null) {
        // an error has been reported above; we won't fill in .ResolvedExpression, but we still must fill in .Type
        e.Type = new InferredTypeProxy();
      } else {
        e.ResolvedExpression = r;
        e.Type = r.Type;
      }
      return null;
    }

    /// <summary>
    /// the return value is false iff there is an error in resolving the datatype value;
    /// if there is an error then an error message is emitted iff complain is true
    /// </summary>
    private bool ResolveDatatypeValue(ResolutionContext resolutionContext, DatatypeValue dtv, DatatypeDecl dt, Type ty, bool complain = true) {
      Contract.Requires(resolutionContext != null);
      Contract.Requires(dtv != null);
      Contract.Requires(dt != null);
      Contract.Requires(ty == null || (ty.AsDatatype == dt && ty.TypeArgs.Count == dt.TypeArgs.Count));

      var ok = true;
      var gt = new List<Type>(dt.TypeArgs.Count);
      var subst = new Dictionary<TypeParameter, Type>();
      for (int i = 0; i < dt.TypeArgs.Count; i++) {
        Type t = ty == null ? new InferredTypeProxy() : ty.TypeArgs[i];
        gt.Add(t);
        dtv.InferredTypeArgs.Add(t);
        subst.Add(dt.TypeArgs[i], t);
      }
      // Construct a resolved type directly, as we know the declaration is dt.
      dtv.Type = new UserDefinedType(dtv.tok, dt.Name, dt, gt);

      DatatypeCtor ctor;
      if (!dt.ConstructorsByName.TryGetValue(dtv.MemberName, out ctor)) {
        ok = false;
        if (complain) {
          reporter.Error(MessageSource.Resolver, dtv.tok, "undeclared constructor {0} in datatype {1}", dtv.MemberName, dtv.DatatypeName);
        }
      } else {
        Contract.Assert(ctor != null);  // follows from postcondition of TryGetValue
        dtv.Ctor = ctor;
      }
      if (complain && ctor != null) {
        ResolveActualParameters(dtv.Bindings, ctor.Formals, dtv.tok, ctor, resolutionContext, subst, null);
      } else {
        // still resolve the expressions
        foreach (var binding in dtv.Bindings.ArgumentBindings) {
          ResolveExpression(binding.Actual, resolutionContext);
        }
        dtv.Bindings.AcceptArgumentExpressionsAsExactParameterList();
      }

      return ok && ctor.Formals.Count == dtv.Arguments.Count;
    }

    public void ResolveFunctionCallExpr(FunctionCallExpr e, ResolutionContext resolutionContext) {
      Contract.Requires(e != null);
      Contract.Requires(e.Type == null);  // should not have been type checked before

      ResolveReceiver(e.Receiver, resolutionContext);
      Contract.Assert(e.Receiver.Type != null);  // follows from postcondition of ResolveExpression

      NonProxyType tentativeReceiverType;
      var member = ResolveMember(e.tok, e.Receiver.Type, e.Name, out tentativeReceiverType);
#if !NO_WORK_TO_BE_DONE
      var ctype = (UserDefinedType)tentativeReceiverType;
#endif
      if (member == null) {
        // error has already been reported by ResolveMember
      } else if (member is Method) {
        reporter.Error(MessageSource.Resolver, e, "member {0} in type {1} refers to a method, but only functions can be used in this context", e.Name, cce.NonNull(ctype).Name);
      } else if (!(member is Function)) {
        reporter.Error(MessageSource.Resolver, e, "member {0} in type {1} does not refer to a function", e.Name, cce.NonNull(ctype).Name);
      } else {
        Function function = (Function)member;
        e.Function = function;
        if (function is TwoStateFunction && !resolutionContext.IsTwoState) {
          reporter.Error(MessageSource.Resolver, e.tok, "a two-state function can be used only in a two-state context");
        }
        if (e.Receiver is StaticReceiverExpr && !function.IsStatic) {
          reporter.Error(MessageSource.Resolver, e, "an instance function must be selected via an object, not just a class name");
        }
        Contract.Assert(ctype != null);  // follows from postcondition of ResolveMember
        if (!function.IsStatic) {
          if (!scope.AllowInstance && e.Receiver is ThisExpr) {
            // The call really needs an instance, but that instance is given as 'this', which is not
            // available in this context.  In most cases, occurrences of 'this' inside e.Receiver would
            // have been caught in the recursive call to resolve e.Receiver, but not the specific case
            // of e.Receiver being 'this' (explicitly or implicitly), for that case needs to be allowed
            // in the event that a static function calls another static function (and note that we need the
            // type of the receiver in order to find the method, so we could not have made this check
            // earlier).
            reporter.Error(MessageSource.Resolver, e.Receiver, "'this' is not allowed in a 'static' context");
          } else if (e.Receiver is StaticReceiverExpr) {
            reporter.Error(MessageSource.Resolver, e.Receiver, "call to instance function requires an instance");
          }
        }
        // build the type substitution map
        var typeMap = new Dictionary<TypeParameter, Type>();
        for (int i = 0; i < ctype.TypeArgs.Count; i++) {
          typeMap.Add(ctype.ResolvedClass.TypeArgs[i], ctype.TypeArgs[i]);
        }
        var typeThatEnclosesMember = ctype.AsParentType(member.EnclosingClass);
        e.TypeApplication_AtEnclosingClass = new List<Type>();
        for (int i = 0; i < typeThatEnclosesMember.TypeArgs.Count; i++) {
          e.TypeApplication_AtEnclosingClass.Add(typeThatEnclosesMember.TypeArgs[i]);
        }
        e.TypeApplication_JustFunction = new List<Type>();
        foreach (TypeParameter p in function.TypeArgs) {
          var ty = new ParamTypeProxy(p);
          typeMap.Add(p, ty);
          e.TypeApplication_JustFunction.Add(ty);
        }
        Dictionary<TypeParameter, Type> subst = BuildTypeArgumentSubstitute(typeMap);

        // type check the arguments
        ResolveActualParameters(e.Bindings, function.Formals, e.tok, function, resolutionContext, subst, function.IsStatic ? null : e.Receiver);

        e.Type = function.ResultType.Subst(subst).NormalizeExpand();
      }
    }

    void ResolveReceiver(Expression expr, ResolutionContext resolutionContext) {
      Contract.Requires(expr != null);
      Contract.Ensures(expr.Type != null);

      if (expr is ThisExpr && !expr.WasResolved()) {
        // Allow 'this' here, regardless of scope.AllowInstance.  The caller is responsible for
        // making sure 'this' does not really get used when it's not available.
        Contract.Assume(currentClass != null);  // this is really a precondition, in this case
        expr.Type = GetThisType(expr.tok, currentClass);
      } else {
        ResolveExpression(expr, resolutionContext);
      }
    }

    void ResolveSeqSelectExpr(SeqSelectExpr e, ResolutionContext resolutionContext) {
      Contract.Requires(e != null);
      if (e.Type != null) {
        // already resolved
        return;
      }

      ResolveExpression(e.Seq, resolutionContext);
      Contract.Assert(e.Seq.Type != null);  // follows from postcondition of ResolveExpression

      if (e.SelectOne) {
        AddXConstraint(e.tok, "Indexable", e.Seq.Type, "element selection requires a sequence, array, multiset, or map (got {0})");
        ResolveExpression(e.E0, resolutionContext);
        AddXConstraint(e.E0.tok, "ContainerIndex", e.Seq.Type, e.E0.Type, "incorrect type for selection into {0} (got {1})");
        Contract.Assert(e.E1 == null);
        e.Type = new InferredTypeProxy() { KeepConstraints = true };
        AddXConstraint(e.tok, "ContainerResult",
          e.Seq.Type, e.Type,
          new SeqSelectOneErrorMsg(e.tok, e.Seq.Type, e.Type));
      } else {
        AddXConstraint(e.tok, "MultiIndexable", e.Seq.Type, "multi-selection of elements requires a sequence or array (got {0})");
        if (e.E0 != null) {
          ResolveExpression(e.E0, resolutionContext);
          AddXConstraint(e.E0.tok, "ContainerIndex", e.Seq.Type, e.E0.Type, "incorrect type for selection into {0} (got {1})");
          ConstrainSubtypeRelation(NewIntegerBasedProxy(e.tok), e.E0.Type, e.E0, "wrong number of indices for multi-selection");
        }
        if (e.E1 != null) {
          ResolveExpression(e.E1, resolutionContext);
          AddXConstraint(e.E1.tok, "ContainerIndex", e.Seq.Type, e.E1.Type, "incorrect type for selection into {0} (got {1})");
          ConstrainSubtypeRelation(NewIntegerBasedProxy(e.tok), e.E1.Type, e.E1, "wrong number of indices for multi-selection");
        }
        var resultType = new InferredTypeProxy() { KeepConstraints = true };
        e.Type = new SeqType(resultType);
        AddXConstraint(e.tok, "ContainerResult", e.Seq.Type, resultType, "multi-selection has type {0} which is incompatible with expected type {1}");
      }
    }

  }

  public class MethodCallInformation {
    public readonly IToken Tok;
    public readonly MemberSelectExpr Callee;
    public readonly List<ActualBinding> ActualParameters;

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Tok != null);
      Contract.Invariant(Callee != null);
      Contract.Invariant(Callee.Member is Method);
      Contract.Invariant(ActualParameters != null);
    }

    public MethodCallInformation(IToken tok, MemberSelectExpr callee, List<ActualBinding> actualParameters) {
      Contract.Requires(tok != null);
      Contract.Requires(callee != null);
      Contract.Requires(callee.Member is Method);
      Contract.Requires(actualParameters != null);
      this.Tok = tok;
      this.Callee = callee;
      this.ActualParameters = actualParameters;
    }
  }
}
