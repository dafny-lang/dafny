//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

/// <summary>
/// The purpose of the PreTypeToTypeVisitor is to fill in a type to each expression and other AST nodes where types make
/// sense. This computation of this type draws from two sources:
///    - the pre-type inferred earlier
///    - any user-supplied type
/// For most AST nodes, this will not consider subset types; instead, subset types are considered later during
/// the type adjustment phase.
///
/// Of the types filled in here, three special TypeProxy's are used.
///    - AdjustableType
///    - BottomTypePlaceholder
///    - ExactTypePlaceholder
/// </summary>
class PreTypeToTypeVisitor : ASTVisitor<IASTVisitorContext> {
  public override IASTVisitorContext GetContext(IASTVisitorContext astVisitorContext, bool inFunctionPostcondition) {
    return astVisitorContext;
  }

  private readonly SystemModuleManager systemModuleManager;

  public PreTypeToTypeVisitor(SystemModuleManager systemModuleManager) {
    this.systemModuleManager = systemModuleManager;
  }

  protected override void VisitOneDeclaration(TopLevelDecl decl) {
    if (decl is NewtypeDecl newtypeDecl) {
      TypeAdjustments.Combine(newtypeDecl.BaseType, newtypeDecl.BasePreType, false);
    } else if (decl is SubsetTypeDecl subsetTypeDecl) {
      TypeAdjustments.Combine(subsetTypeDecl.Var.Type, subsetTypeDecl.Var.PreType, false);
    }

    base.VisitOneDeclaration(decl);
  }

  public override void VisitField(Field field) {
    if (field is ConstantField constField) {
      // The type of the const might have been omitted in the program text and then inferred
      TypeAdjustments.Combine(constField.Type, constField.PreType, true);
    }

    base.VisitField(field);
  }

  private static void VisitVariableList(IEnumerable<IVariable> variables, bool allowFutureAdjustments) {
    foreach (var v in variables) {
      TypeAdjustments.Combine(v.Type, v.PreType, allowFutureAdjustments);
    }
  }

  protected override void PostVisitOneExpression(Expression expr, IASTVisitorContext context) {
    if (expr is FunctionCallExpr functionCallExpr) {
      functionCallExpr.TypeApplication_AtEnclosingClass = functionCallExpr.PreTypeApplication_AtEnclosingClass.ConvertAll(TypeAdjustments.PreType2FixedType);
      functionCallExpr.TypeApplication_JustFunction = functionCallExpr.PreTypeApplication_JustFunction.ConvertAll(TypeAdjustments.PreType2FixedType);
    } else if (expr is MemberSelectExpr memberSelectExpr) {
      memberSelectExpr.TypeApplication_AtEnclosingClass = memberSelectExpr.PreTypeApplication_AtEnclosingClass.ConvertAll(TypeAdjustments.PreType2FixedType);
      memberSelectExpr.TypeApplication_JustMember = memberSelectExpr.PreTypeApplication_JustMember.ConvertAll(TypeAdjustments.PreType2FixedType);
    } else if (expr is ComprehensionExpr comprehensionExpr) {
      VisitVariableList(comprehensionExpr.BoundVars, false);
    } else if (expr is LetExpr letExpr) {
      VisitVariableList(letExpr.BoundVars, letExpr.Exact);
      foreach (var lhs in letExpr.LHSs) {
        VisitPattern(lhs, context);
      }
    } else if (expr is DatatypeValue datatypeValue) {
      Contract.Assert(datatypeValue.InferredTypeArgs.Count == 0 || datatypeValue.InferredTypeArgs.Count == datatypeValue.InferredPreTypeArgs.Count);
      if (datatypeValue.InferredTypeArgs.Count == 0) {
        foreach (var preTypeArgument in datatypeValue.InferredPreTypeArgs) {
          datatypeValue.InferredTypeArgs.Add(TypeAdjustments.PreType2FixedType(preTypeArgument));
        }
      }
    } else if (expr is ConversionExpr conversionExpr) {
      TypeAdjustments.Combine(conversionExpr.ToType, conversionExpr.PreType, false);
    }

    if (expr.PreType is UnusedPreType) {
      expr.Type = new InferredTypeProxy();
    } else if (expr is ConcreteSyntaxExpression { ResolvedExpression: { } resolvedExpression }) {
      expr.UnnormalizedType = resolvedExpression.UnnormalizedType;
    } else if (expr is SeqSelectExpr { Seq: { Type: { AsMultiSetType: { } } } }) {
      expr.UnnormalizedType = systemModuleManager.Nat();
    } else {
      expr.UnnormalizedType = TypeAdjustments.PreType2AdjustableType(expr.PreType, TypeParameter.TPVariance.Co);
    }
    base.PostVisitOneExpression(expr, context);
  }

  private void VisitPattern<VT>(CasePattern<VT> casePattern, IASTVisitorContext context) where VT : class, IVariable {
    if (casePattern.Var != null) {
      TypeAdjustments.Combine(casePattern.Var.Type, casePattern.Var.PreType, false);
    }
    VisitExpression(casePattern.Expr, context);

    casePattern.Arguments?.ForEach(v => VisitPattern(v, context));
  }

  protected override bool VisitOneStatement(Statement stmt, IASTVisitorContext context) {
    if (stmt is VarDeclStmt varDeclStmt) {
      VisitVariableList(varDeclStmt.Locals, true);
    } else if (stmt is VarDeclPattern varDeclPattern) {
      VisitVariableList(varDeclPattern.LocalVars, true);
    } else if (stmt is ForLoopStmt forLoopStmt) {
      TypeAdjustments.Combine(forLoopStmt.LoopIndex.Type, forLoopStmt.LoopIndex.PreType, false);
    } else if (stmt is ForallStmt forallStmt) {
      VisitVariableList(forallStmt.BoundVars, false);
    }

    return base.VisitOneStatement(stmt, context);
  }

  protected override void PostVisitOneStatement(Statement stmt, IASTVisitorContext context) {
    if (stmt is VarDeclPattern varDeclPattern) {
      VisitPattern(varDeclPattern.LHS, context);
    } else if (stmt is AssignStmt { Rhs: TypeRhs tRhs }) {
      Type rhsType;
      // convert the type of the RHS, which we expect to be a reference type, and then create the non-null version of it
      var udtConvertedFromPretype = (UserDefinedType)TypeAdjustments.PreType2FixedType(tRhs.PreType);
      Contract.Assert(udtConvertedFromPretype.IsRefType);
      if (tRhs.ArrayDimensions != null) {
        // In this case, we expect tRhs.PreType (and udtConvertedFromPretype) to be an array type
        var arrayPreType = (DPreType)tRhs.PreType.Normalize();
        Contract.Assert(arrayPreType.Decl is ArrayClassDecl);
        Contract.Assert(arrayPreType.Arguments.Count == 1);
        Contract.Assert(udtConvertedFromPretype.ResolvedClass is ArrayClassDecl);
        Contract.Assert(udtConvertedFromPretype.TypeArgs.Count == 1);

        // The user-supplied tRhs.EType may have some components that are more exact than what's in udtConvertedFromPretype, since
        // tRhs.EType may contain user-supplied subset types. But tRhs.EType may also be missing some type arguments altogether, because
        // they may have been omitted in the source text. The following has the effect of filling in any such missing components with
        // whatever was inferred during pre-type inference.
        TypeAdjustments.Combine(tRhs.EType, arrayPreType.Arguments[0], false);
        var arrayTypeDecl = systemModuleManager.arrayTypeDecls[tRhs.ArrayDimensions.Count];
        var rhsMaybeNullType = new UserDefinedType(stmt.tok, arrayTypeDecl.Name, arrayTypeDecl, new List<Type>() { tRhs.EType });
        rhsType = UserDefinedType.CreateNonNullType(rhsMaybeNullType);
      } else {
        // Fill in any missing type arguments in the user-supplied tRhs.EType.
        TypeAdjustments.Combine(tRhs.EType, tRhs.PreType, false);
        rhsType = (UserDefinedType)tRhs.EType;
        if (tRhs.InitCall != null) {
          // We want the type of tRhs.InitCall.MethodSelect.Obj to be the same as what the "new" gives, but the previous
          // visitation of this MemberSelectExpr would have set it to the type obtained from the pre-type. Since the MemberSelectExpr
          // won't be visited again during type adjustment, we set it here once and for all.
          tRhs.InitCall.MethodSelect.Obj.UnnormalizedType = rhsType;
        }
      }
      tRhs.Type = rhsType;

    } else if (stmt is AssignSuchThatStmt assignSuchThatStmt) {
      foreach (var lhs in assignSuchThatStmt.Lhss) {
        VisitExpression(lhs, context);
      }

    } else if (stmt is ProduceStmt produceStmt) {
      if (produceStmt.HiddenUpdate != null) {
        VisitStatement(produceStmt.HiddenUpdate, context);
      }

    } else if (stmt is CalcStmt calcStmt) {
      // The expression in each line has been visited, but pairs of those lines are then put together to
      // form steps. These steps (are always boolean, and) need to be visited, too. Their subexpressions
      // have already been visited, so it suffices to call PostVisitOneExpression (instead of VisitExpression)
      // here.
      foreach (var step in calcStmt.Steps) {
        PostVisitOneExpression(step, context);
      }
      PostVisitOneExpression(calcStmt.Result, context);
    }

    base.PostVisitOneStatement(stmt, context);
  }

  protected override void VisitExtendedPattern(ExtendedPattern pattern, IASTVisitorContext context) {
    switch (pattern) {
      case DisjunctivePattern disjunctivePattern:
        break;
      case LitPattern litPattern:
        PostVisitOneExpression(litPattern.OptimisticallyDesugaredLit, context);
        break;
      case IdPattern idPattern:
        if (idPattern.BoundVar != null) {
          TypeAdjustments.Combine(idPattern.BoundVar.Type, idPattern.BoundVar.PreType, false);
        }
        if (idPattern.ResolvedLit != null) {
          PostVisitOneExpression(idPattern.ResolvedLit, context);
        }
        break;
      default:
        Contract.Assert(false); // unexpected case
        break;
    }
    base.VisitExtendedPattern(pattern, context);
  }

}
