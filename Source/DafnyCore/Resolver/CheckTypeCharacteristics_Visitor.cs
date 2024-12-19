using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

/// <summary>
/// This visitor checks that type characteristics are respected in all (implicitly or explicitly)
/// declared types. Note that equality-support is checked only in compiled contexts.
/// In addition, this visitor checks that operations that require equality are applied to
/// types that really do support equality; this, too, is checked only in compiled contexts.
/// </summary>
class CheckTypeCharacteristics_Visitor : ResolverTopDownVisitor<bool> {
  public CheckTypeCharacteristics_Visitor(ErrorReporter reporter)
    : base(reporter) {
    Contract.Requires(reporter != null);
  }


  public static bool CanCompareWith(Expression expr) {
    Contract.Requires(expr != null);
    if (expr.Type.SupportsEquality) {
      return true;
    }
    expr = expr.Resolved;
    if (expr is DatatypeValue datatypeValue && !datatypeValue.Ctor.EnclosingDatatype.HasGhostVariant) {
      for (var i = 0; i < datatypeValue.Ctor.Formals.Count; i++) {
        if (datatypeValue.Ctor.Formals[i].IsGhost) {
          return false;
        } else if (!CanCompareWith(datatypeValue.Arguments[i])) {
          return false;
        }
      }
      return true;
    } else if (expr is DisplayExpression) {
      var e = (DisplayExpression)expr;
      return e.Elements.Count == 0;
    } else if (expr is MapDisplayExpr) {
      var e = (MapDisplayExpr)expr;
      return e.Elements.Count == 0;
    }
    return false;
  }

  protected override bool VisitOneStmt(Statement stmt, ref bool inGhostContext) {
    if (stmt.IsGhost) {
      inGhostContext = true;
    }
    // In the sequel, do two things:
    //  * Call VisitType on any type that occurs in the statement
    //  * If the statement introduces ghost components, handle those components here
    //    rather than letting the default visitor handle them
    if (stmt is VarDeclStmt) {
      var s = (VarDeclStmt)stmt;
      foreach (var v in s.Locals) {
        VisitType(v.Tok, v.Type, inGhostContext || v.IsGhost);
      }
    } else if (stmt is VarDeclPattern) {
      var s = (VarDeclPattern)stmt;
      foreach (var v in s.LocalVars) {
        VisitType(v.Tok, v.Type, inGhostContext || v.IsGhost);
      }
    } else if (stmt is SingleAssignStmt) {
      var s = (SingleAssignStmt)stmt;
      if (s.Rhs is TypeRhs tRhs) {
        VisitType(tRhs.Tok, tRhs.Type, inGhostContext);
      }
    } else if (stmt is AssignSuchThatStmt) {
      var s = (AssignSuchThatStmt)stmt;
      Visit(Attributes.SubExpressions(s.Attributes), true);
      Visit(s.Expr, inGhostContext);
      foreach (var lhs in s.Lhss) {
        Visit(lhs, inGhostContext);
      }
      return false;
    } else if (stmt is WhileStmt) {
      var s = (WhileStmt)stmt;
      // all subexpressions are ghost, except the guard
      Visit(s.LoopSpecificationExpressions, true);
      if (s.Guard != null) {
        Visit(s.Guard, inGhostContext);
      }
      Visit(s.SubStatements, inGhostContext);
      return false;
    } else if (stmt is AlternativeLoopStmt) {
      var s = (AlternativeLoopStmt)stmt;
      // all subexpressions are ghost, except the guards
      Visit(s.LoopSpecificationExpressions, true);
      foreach (var alt in s.Alternatives) {
        Visit(alt.Guard, inGhostContext);
      }
      Visit(s.SubStatements, inGhostContext);
      return false;
    } else if (stmt is ForLoopStmt) {
      var s = (ForLoopStmt)stmt;
      // all subexpressions are ghost, except the bounds
      Visit(s.LoopSpecificationExpressions, true);
      Visit(s.Start, inGhostContext);
      if (s.End != null) {
        Visit(s.End, inGhostContext);
      }
      Visit(s.SubStatements, inGhostContext);
      return false;
    } else if (stmt is CallStmt) {
      var s = (CallStmt)stmt;
      CheckTypeInstantiation(s.Tok, s.Method.WhatKind, s.Method.Name, s.Method.TypeArgs, s.MethodSelect.TypeApplicationJustMember, inGhostContext);
      // recursively visit all subexpressions, noting that some of them may correspond to ghost formal parameters
      Contract.Assert(s.Lhs.Count == s.Method.Outs.Count);
      for (var i = 0; i < s.Method.Outs.Count; i++) {
        Visit(s.Lhs[i], inGhostContext || s.Method.Outs[i].IsGhost);
      }
      Visit(s.Receiver, inGhostContext);
      Contract.Assert(s.Args.Count == s.Method.Ins.Count);
      for (var i = 0; i < s.Method.Ins.Count; i++) {
        Visit(s.Args[i], inGhostContext || s.Method.Ins[i].IsGhost);
      }
      return false;
    } else if (stmt is ForallStmt) {
      var s = (ForallStmt)stmt;
      foreach (var v in s.BoundVars) {
        VisitType(v.Tok, v.Type, inGhostContext);
      }
      // do substatements and subexpressions, noting that ensures clauses are ghost
      Visit(Attributes.SubExpressions(s.Attributes), true);
      if (s.Range != null) {
        Visit(s.Range, inGhostContext);
      }
      foreach (var ee in s.Ens) {
        Visit(Attributes.SubExpressions(ee.Attributes), true);
        Visit(ee.E, true);
      }
      Visit(s.SubStatements, inGhostContext);
      return false;
    } else if (stmt is ExpectStmt) {
      var s = (ExpectStmt)stmt;
      Visit(Attributes.SubExpressions(s.Attributes), true);
      Visit(s.Expr, inGhostContext);
      if (s.Message != null) {
        Visit(s.Message, inGhostContext);
      }
      return false;
    }
    return true;
  }

  protected override bool VisitOneExpr(Expression expr, ref bool inGhostContext) {
    // Do two things:
    //  * Call VisitType on any type that occurs in the statement
    //  * If the expression introduces ghost components, handle those components here
    //    rather than letting the default visitor handle them
    if (expr is BinaryExpr && !inGhostContext) {
      var e = (BinaryExpr)expr;
      var t0 = e.E0.Type.NormalizeExpand();
      var t1 = e.E1.Type.NormalizeExpand();
      switch (e.Op) {
        case BinaryExpr.Opcode.Eq:
        case BinaryExpr.Opcode.Neq:
          if (t0.IsTraitType || t1.IsTraitType) {
            // Non-reference-type traits do not support equality, but reference-trait types do.
            if (!t0.SupportsEquality) {
              reporter.Error(MessageSource.Resolver, e.E0, "{0} can only be applied to expressions of types that support equality (got {1}){2}", BinaryExpr.OpcodeString(e.Op), t0, TypeEqualityErrorMessageHint(t0));
            } else if (!t1.SupportsEquality) {
              reporter.Error(MessageSource.Resolver, e.E1, "{0} can only be applied to expressions of types that support equality (got {1}){2}", BinaryExpr.OpcodeString(e.Op), t1, TypeEqualityErrorMessageHint(t1));
            }
          } else if (CanCompareWith(e.E0) || CanCompareWith(e.E1)) {
            // These are special cases with values that can always be compared against--for example, a datatype value (like Nil) that takes no parameters
          } else if (!t0.PartiallySupportsEquality) {
            reporter.Error(MessageSource.Resolver, e.E0, "{0} can only be applied to expressions of types that support equality (got {1}){2}", BinaryExpr.OpcodeString(e.Op), t0, TypeEqualityErrorMessageHint(t0));
          } else if (!t1.PartiallySupportsEquality) {
            reporter.Error(MessageSource.Resolver, e.E1, "{0} can only be applied to expressions of types that support equality (got {1}){2}", BinaryExpr.OpcodeString(e.Op), t1, TypeEqualityErrorMessageHint(t1));
          }
          break;
        default:
          switch (e.ResolvedOp) {
            // Note, all operations on sets, multisets, and maps are guaranteed to work because of restrictions placed on how
            // these types are instantiated.  (Except: This guarantee does not apply to equality on maps, because the Range type
            // of maps is not restricted, only the Domain type.  However, the equality operator is checked above.)
            case BinaryExpr.ResolvedOpcode.InSeq:
            case BinaryExpr.ResolvedOpcode.NotInSeq:
            case BinaryExpr.ResolvedOpcode.Prefix:
            case BinaryExpr.ResolvedOpcode.ProperPrefix:
              if (!t1.SupportsEquality) {
                reporter.Error(MessageSource.Resolver, e.E1, "{0} can only be applied to expressions of sequence types that support equality (got {1}){2}", BinaryExpr.OpcodeString(e.Op), t1, TypeEqualityErrorMessageHint(t1));
              } else if (!t0.SupportsEquality) {
                if (e.ResolvedOp == BinaryExpr.ResolvedOpcode.InSet || e.ResolvedOp == BinaryExpr.ResolvedOpcode.NotInSeq) {
                  reporter.Error(MessageSource.Resolver, e.E0, "{0} can only be applied to expressions of types that support equality (got {1}){2}", BinaryExpr.OpcodeString(e.Op), t0, TypeEqualityErrorMessageHint(t0));
                } else {
                  reporter.Error(MessageSource.Resolver, e.E0, "{0} can only be applied to expressions of sequence types that support equality (got {1}){2}", BinaryExpr.OpcodeString(e.Op), t0, TypeEqualityErrorMessageHint(t0));
                }
              }
              break;
            default:
              break;
          }
          break;
      }
    } else if (expr is ComprehensionExpr) {
      var e = (ComprehensionExpr)expr;
      foreach (var bv in e.BoundVars) {
        VisitType(bv.Tok, bv.Type, inGhostContext);
      }
    } else if (expr is LetExpr) {
      var e = (LetExpr)expr;
      Visit(Attributes.SubExpressions(e.Attributes), true);
      if (e.Exact) {
        Contract.Assert(e.LHSs.Count == e.RHSs.Count);
        for (var i = 0; i < e.LHSs.Count; i++) {
          // The VisitPattern function visits all BoundVar's in a pattern and returns
          // "true" if all variables are ghost.
          bool VisitPattern(CasePattern<BoundVar> pat, bool patternGhostContext) {
            if (pat.Var != null) {
              VisitType(pat.Tok, pat.Var.Type, patternGhostContext || pat.Var.IsGhost);
              return pat.Var.IsGhost;
            } else {
              var allGhost = true;
              Contract.Assert(pat.Ctor != null);
              Contract.Assert(pat.Ctor.Formals.Count == pat.Arguments.Count);
              for (var i = 0; i < pat.Ctor.Formals.Count; i++) {
                var formal = pat.Ctor.Formals[i];
                var arg = pat.Arguments[i];
                // don't use short-circuit booleans in the following line, because we want to visit all nested patterns
                allGhost &= VisitPattern(arg, patternGhostContext || formal.IsGhost);
              }
              return allGhost;
            }
          }

          var allGhosts = VisitPattern(e.LHSs[i], inGhostContext);
          Visit(e.RHSs[i], inGhostContext || allGhosts);
        }
      } else {
        Contract.Assert(e.RHSs.Count == 1);
        var allGhost = true;
        foreach (var bv in e.BoundVars) {
          if (!bv.IsGhost) {
            allGhost = false;
          }
          VisitType(bv.Tok, bv.Type, inGhostContext || bv.IsGhost);
        }
        Visit(e.RHSs[0], inGhostContext || allGhost);
      }
      Visit(e.Body, inGhostContext);
      return false;
    } else if (expr is MemberSelectExpr) {
      var e = (MemberSelectExpr)expr;
      if (e.Member is Function || e.Member is Method) {
        CheckTypeInstantiation(e.Tok, e.Member.WhatKind, e.Member.Name, ((ICallable)e.Member).TypeArgs, e.TypeApplicationJustMember, inGhostContext);
      }
    } else if (expr is FunctionCallExpr) {
      var e = (FunctionCallExpr)expr;
      CheckTypeInstantiation(e.Tok, e.Function.WhatKind, e.Function.Name, e.Function.TypeArgs, e.TypeApplication_JustFunction, inGhostContext);
      // recursively visit all subexpressions (all actual parameters), noting which ones correspond to ghost formal parameters
      Visit(e.Receiver, inGhostContext);
      Contract.Assert(e.Args.Count == e.Function.Ins.Count);
      for (var i = 0; i < e.Args.Count; i++) {
        Visit(e.Args[i], inGhostContext || e.Function.Ins[i].IsGhost);
      }
      return false;  // we've done what there is to be done
    } else if (expr is DatatypeValue) {
      var e = (DatatypeValue)expr;
      VisitType(expr.Tok, expr.Type, inGhostContext);
      // recursively visit all subexpressions (all actual parameters), noting which ones correspond to ghost formal parameters
      Contract.Assert(e.Arguments.Count == e.Ctor.Formals.Count);
      for (var i = 0; i < e.Arguments.Count; i++) {
        Visit(e.Arguments[i], inGhostContext || e.Ctor.Formals[i].IsGhost);
      }
      return false;  // we've done what there is to be done
    } else if (expr is SetDisplayExpr || expr is MultiSetDisplayExpr || expr is MapDisplayExpr || expr is SeqConstructionExpr ||
               expr is MultiSetFormingExpr || expr is StaticReceiverExpr) {
      // This catches other expressions whose type may potentially be illegal
      VisitType(expr.Tok, expr.Type, inGhostContext);
    } else if (expr is StmtExpr) {
      var e = (StmtExpr)expr;
      Visit(e.S, true);
      Visit(e.E, inGhostContext);
      return false;
    }
    return true;
  }

  public void VisitType(IOrigin tok, Type type, bool inGhostContext) {
    Contract.Requires(tok != null);
    Contract.Requires(type != null);
    type = type.Normalize();  // we only do a .Normalize() here, because we want to stop at any type synonym or subset type
    if (type is BasicType) {
      // fine
    } else if (type is SetType) {
      var st = (SetType)type;
      var argType = st.Arg;
      if (!inGhostContext && !argType.SupportsEquality) {
        reporter.Error(MessageSource.Resolver, tok, "{2}set argument type must support equality (got {0}){1}", argType, TypeEqualityErrorMessageHint(argType), st.Finite ? "" : "i");
      }
      VisitType(tok, argType, inGhostContext);

    } else if (type is MultiSetType) {
      var argType = ((MultiSetType)type).Arg;
      if (!inGhostContext && !argType.SupportsEquality) {
        reporter.Error(MessageSource.Resolver, tok, "multiset argument type must support equality (got {0}){1}", argType, TypeEqualityErrorMessageHint(argType));

      }
      VisitType(tok, argType, inGhostContext);
    } else if (type is MapType) {
      var mt = (MapType)type;
      if (!inGhostContext && !mt.Domain.SupportsEquality) {
        reporter.Error(MessageSource.Resolver, tok, "{2}map domain type must support equality (got {0}){1}", mt.Domain, TypeEqualityErrorMessageHint(mt.Domain), mt.Finite ? "" : "i");
      }
      VisitType(tok, mt.Domain, inGhostContext);
      VisitType(tok, mt.Range, inGhostContext);

    } else if (type is SeqType) {
      Type argType = ((SeqType)type).Arg;
      VisitType(tok, argType, inGhostContext);

    } else if (type is UserDefinedType) {
      var udt = (UserDefinedType)type;
      Contract.Assert(udt.ResolvedClass != null);
      var formalTypeArgs = udt.ResolvedClass.TypeArgs;
      Contract.Assert(formalTypeArgs != null);
      CheckTypeInstantiation(udt.Tok, "type", udt.ResolvedClass.Name, formalTypeArgs, udt.TypeArgs, inGhostContext);

    } else if (type is TypeProxy) {
      // the type was underconstrained; this is checked elsewhere, but it is not in violation of the equality-type test
    } else {
      Contract.Assert(false); throw new cce.UnreachableException();  // unexpected type
    }
  }

  void CheckTypeInstantiation(IOrigin tok, string what, string className, List<TypeParameter> formalTypeArgs, List<Type> actualTypeArgs, bool inGhostContext) {
    Contract.Requires(tok != null);
    Contract.Requires(what != null);
    Contract.Requires(className != null);
    Contract.Requires(formalTypeArgs != null);
    Contract.Requires(actualTypeArgs != null);
    Contract.Requires(formalTypeArgs.Count == actualTypeArgs.Count);

    var typeMap = TypeParameter.SubstitutionMap(formalTypeArgs, actualTypeArgs);
    for (var i = 0; i < formalTypeArgs.Count; i++) {
      var formal = formalTypeArgs[i];
      var actual = actualTypeArgs[i];
      if (!CheckCharacteristics(formal.Characteristics, actual, inGhostContext, out var whatIsNeeded, out var hint, out _)) {
        var index = actualTypeArgs.Count == 1 ? "" : " " + i;
        reporter.Error(MessageSource.Resolver, tok,
          $"type parameter{index} ({formal.Name}) passed to {what} {className} must {whatIsNeeded} (got {actual}){hint}");
      }
      VisitType(tok, actual, inGhostContext);
      foreach (var typeBound in formal.TypeBounds) {
        var bound = typeBound.Subst(typeMap);
        if (!Type.IsSupertype(bound, actual) || (actual.IsRefType && !actual.IsNonNullRefType && !bound.IsRefType)) {
          var index = actualTypeArgs.Count == 1 ? "" : " " + i;
          reporter.Error(MessageSource.Resolver, tok,
            $"type parameter{index} ('{formal.Name}') passed to {what} '{className}' must meet type bound '{bound}' (got '{actual}')");
        }
      }
    }
  }

  /// <summary>
  /// Grammatically, "whatIsNeeded" is an imperative that says what to do to be in compliance. Concretely, it is one of the following
  /// strings (not including the words in square brackets):
  ///     * [type X must] contain no references
  ///     * [type X must] support equality
  ///     * [type X must] support auto-initialization
  ///     * [type X must] be nonempty
  /// </summary>
  public static bool CheckCharacteristics(TypeParameter.TypeParameterCharacteristics formal, Type actual, bool inGhostContext,
    out string whatIsNeeded, out string hint, out RefinementErrors.ErrorId errorId) {
    Contract.Ensures(Contract.Result<bool>() || (Contract.ValueAtReturn(out whatIsNeeded) != null && Contract.ValueAtReturn(out hint) != null));
    if (!inGhostContext && formal.EqualitySupport != TypeParameter.EqualitySupportValue.Unspecified && !actual.SupportsEquality) {
      whatIsNeeded = "support equality";
      hint = TypeEqualityErrorMessageHint(actual);
      errorId = RefinementErrors.ErrorId.ref_mismatched_type_characteristics_equality;
      return false;
    }
    var cl = (actual.Normalize() as UserDefinedType)?.ResolvedClass;
    var tp = (TopLevelDecl)(cl as TypeParameter) ?? cl as AbstractTypeDecl;
    if (formal.HasCompiledValue && (inGhostContext ? !actual.IsNonempty : !actual.HasCompilableValue)) {
      whatIsNeeded = "support auto-initialization";
      hint = tp == null ? "" :
        string.Format(" (perhaps try declaring {2} '{0}' on line {1} as '{0}(0)', which says it can only be instantiated with a type that supports auto-initialization)", tp.Name, tp.Tok.line, tp.WhatKind);
      errorId = RefinementErrors.ErrorId.ref_mismatched_type_characteristics_autoinit;
      return false;
    }
    if (formal.IsNonempty && !actual.IsNonempty) {
      whatIsNeeded = "be nonempty";
      hint = tp == null ? "" :
        string.Format(" (perhaps try declaring {2} '{0}' on line {1} as '{0}(00)', which says it can only be instantiated with a nonempty type)", tp.Name, tp.Tok.line, tp.WhatKind);
      errorId = RefinementErrors.ErrorId.ref_mismatched_type_characteristics_nonempty;
      return false;
    }
    if (formal.ContainsNoReferenceTypes && actual.MayInvolveReferences) {
      whatIsNeeded = "contain no references";
      hint = tp == null ? "" :
        string.Format(" (perhaps try declaring {2} '{0}' on line {1} as '{0}(!new)', which says it can only be instantiated with a type that contains no references)", tp.Name, tp.Tok.line, tp.WhatKind);
      errorId = RefinementErrors.ErrorId.ref_mismatched_type_characteristics_noreferences;
      return false;
    }
    whatIsNeeded = null;
    hint = null;
    errorId = 0; // to please the compiler; this value will not be used by the caller
    return true;
  }

  public static string TypeEqualityErrorMessageHint(Type argType) {
    Contract.Requires(argType != null);
    argType = argType.Normalize();
    var cl = (argType as UserDefinedType)?.ResolvedClass;
    var tp = (TopLevelDecl)(cl as TypeParameter) ?? cl as AbstractTypeDecl;
    if (tp != null) {
      return string.Format(" (perhaps try declaring {2} '{0}' on line {1} as '{0}(==)', which says it can only be instantiated with a type that supports equality)", tp.Name, tp.Tok.line, tp.WhatKind);
    }

    var typeArgs = argType.TypeArgs;

    if (argType.AsSeqType != null && typeArgs.Count >= 1) {
      if (TypeEqualityErrorMessageHint(typeArgs[0]) is var messageSeq and not "") {
        return messageSeq;
      }
    }
    if (argType.AsMapType != null &&
        typeArgs.Count >= 2 &&
        TypeEqualityErrorMessageHint(typeArgs[1]) is var messageMap and not "") {
      return messageMap;
    }
    if (argType.AsIndDatatype is { EqualitySupport: IndDatatypeDecl.ES.ConsultTypeArguments } decl) {
      var i = 0;
      foreach (var tParam in decl.TypeArgs) {
        if (tParam.NecessaryForEqualitySupportOfSurroundingInductiveDatatype && i < typeArgs.Count && !typeArgs[i].SupportsEquality && TypeEqualityErrorMessageHint(typeArgs[i]) is var message and not "") {
          return message;
        }
        i++;
      }
    }

    if (argType.AsNewtype is { } newTypeDecl) {
      return TypeEqualityErrorMessageHint(newTypeDecl.RhsWithArgument(argType.TypeArgs));
    }
    return "";
  }
}