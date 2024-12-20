//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

/// <summary>
/// The purpose of the TypeRefinementVisitor is to incorporate subset types into the types that were inferred during
/// pre-type inference. The visitor collects constraints, which are solved by the Solve() method.
/// </summary>
public class TypeRefinementVisitor : ASTVisitor<IASTVisitorContext> {
  private string moduleDescription;
  public override IASTVisitorContext GetContext(IASTVisitorContext astVisitorContext, bool inFunctionPostcondition) {
    return astVisitorContext;
  }

  private readonly SystemModuleManager systemModuleManager;

  public TypeRefinementVisitor(string moduleDescription, SystemModuleManager systemModuleManager) {
    this.moduleDescription = moduleDescription;
    this.systemModuleManager = systemModuleManager;
  }

  private readonly List<Flow> flows = new();

  public void DebugPrint() {
    systemModuleManager.Options.OutputWriter.WriteLine($"--------------------------- type-refinement flows, {moduleDescription}:");
    foreach (var flow in flows) {
      flow.DebugPrint(systemModuleManager.Options.OutputWriter);
    }
    systemModuleManager.Options.OutputWriter.WriteLine($"------------------- (end of type-refinement flows, {moduleDescription})");
  }

  protected override bool VisitOneExpression(Expression expr, IASTVisitorContext context) {
    if (expr is DatatypeUpdateExpr datatypeUpdateExpr) {
      // How a DatatypeUpdateExpr desugars depends on whether or not the expression is ghost, which hasn't been determined
      // yet. So, if there is a difference between the two, then pre-type resolution prepares two different resolved expressions.
      // The choice between these two is done in a later phase during resolution. For now, if there are two, we visit them both.
      // ASTVisitor arranges to visit ResolvedExpression, but we consider ResolvedCompiledExpression here.
      if (datatypeUpdateExpr.ResolvedCompiledExpression != datatypeUpdateExpr.ResolvedExpression) {
        VisitExpression(datatypeUpdateExpr.ResolvedCompiledExpression, context);
      }
    }
    return base.VisitOneExpression(expr, context);
  }

  protected override void PostVisitOneExpression(Expression expr, IASTVisitorContext context) {
    if (expr is IdentifierExpr identifierExpr) {
      flows.Add(new FlowFromType(expr, identifierExpr.Var.UnnormalizedType, identifierExpr.Name));

    } else if (expr is SeqSelectExpr selectExpr) {
      var unnormalizedSeqType = selectExpr.Seq.UnnormalizedType;
      var seqType = selectExpr.Seq.Type.NormalizeToAncestorType();
      if (!selectExpr.SelectOne) {
        var sinkType = selectExpr.Type.NormalizeToAncestorType().AsSeqType;
        flows.Add(new FlowFromType(sinkType.Arg, seqType.TypeArgs[0], expr.Tok));
      } else if (seqType.AsSeqType != null || seqType.IsArrayType) {
        flows.Add(new FlowFromTypeArgument(expr, unnormalizedSeqType, 0));
      } else if (seqType.IsMapType || seqType.IsIMapType) {
        flows.Add(new FlowFromTypeArgument(expr, unnormalizedSeqType, 1));
      } else {
        Contract.Assert(seqType.AsMultiSetType != null);
        // type is fixed, so no flow to set up
      }

    } else if (expr is MultiSelectExpr multiSelectExpr) {
      flows.Add(new FlowFromTypeArgument(expr, multiSelectExpr.Array.UnnormalizedType, 0));

    } else if (expr is ITEExpr iteExpr) {
      flows.Add(new FlowBetweenExpressions(expr, iteExpr.Thn, "if-then"));
      flows.Add(new FlowBetweenExpressions(expr, iteExpr.Els, "if-else"));

    } else if (expr is NestedMatchExpr matchExpr) {
      foreach (var kase in matchExpr.Cases) {
        flows.Add(new FlowBetweenExpressions(expr, kase.Body, "case"));
      }

    } else if (expr is MemberSelectExpr memberSelectExpr) {
      if (memberSelectExpr.Member is Field field) {
        var dPreType = (DPreType)memberSelectExpr.Obj.PreType.Normalize();
        if (dPreType.Decl is ValuetypeDecl valuetypeDecl) {
          flows.Add(new FlowFromComputedType(expr, () => {
            // TypeArgumentSubstitutionsWithParents doesn't work with ValuetypeDecl, so we roll our own type map
            var receiverType = memberSelectExpr.Obj.Type.NormalizeExpand();
            Contract.Assert(receiverType.TypeArgs.Count == valuetypeDecl.TypeArgs.Count);
            var typeMap = TypeParameter.SubstitutionMap(valuetypeDecl.TypeArgs, receiverType.TypeArgs);
            return field.Type.Subst(typeMap);
          }, $".{memberSelectExpr.MemberName}"));
        } else {
          flows.Add(new FlowFromComputedType(expr, () => {
            var typeMap = memberSelectExpr.TypeArgumentSubstitutionsWithParents();
            return field.Type.Subst(typeMap);
          }, $".{memberSelectExpr.MemberName}"));
        }
      } else if (memberSelectExpr.Member is Function function) {
        flows.Add(new FlowFromComputedType(expr, () => {
          var typeMap = memberSelectExpr.TypeArgumentSubstitutionsWithParents();
          return ModuleResolver.SelectAppropriateArrowTypeForFunction(function, typeMap, systemModuleManager);
        }, $".{memberSelectExpr.MemberName}"));
      }

    } else if (expr is FunctionCallExpr functionCallExpr) {
      Contract.Assert(functionCallExpr.Args.Count == functionCallExpr.Function.Ins.Count);
      for (var i = 0; i < functionCallExpr.Args.Count; i++) {
        var formal = functionCallExpr.Function.Ins[i];
        var actual = functionCallExpr.Args[i];
        flows.Add(new FlowBetweenComputedTypes(() => {
          var typeMap = functionCallExpr.TypeArgumentSubstitutionsWithParents();
          return (TypeRefinementWrapper.NormalizeSansBottom(formal).Subst(typeMap), TypeRefinementWrapper.NormalizeSansBottom(actual));
        }, functionCallExpr.Tok, $"{functionCallExpr.Function.Name}({formal.Name} := ...)"));
      }

      flows.Add(new FlowFromComputedType(expr, () => {
        var typeMap = functionCallExpr.TypeArgumentSubstitutionsWithParents();
        return functionCallExpr.Function.ResultType.Subst(typeMap);
      }, $"{functionCallExpr.Name}(...)"));

    } else if (expr is DatatypeValue datatypeValue) {
      var ctor = datatypeValue.Ctor;
      var datatypeDecl = ctor.EnclosingDatatype;
      for (var i = 0; i < datatypeValue.Arguments.Count; i++) {
        var formal = ctor.Formals[i];
        var actual = datatypeValue.Arguments[i];
        flows.Add(new FlowBetweenComputedTypes(() => {
          var typeMap = TypeParameter.SubstitutionMap(datatypeDecl.TypeArgs, datatypeValue.InferredTypeArgs);
          return (TypeRefinementWrapper.NormalizeSansBottom(formal).Subst(typeMap), TypeRefinementWrapper.NormalizeSansBottom(actual));
        }, datatypeValue.Tok, $"{ctor.Name}({formal.Name} := ...)"));
      }
      flows.Add(new FlowFromComputedType(expr,
        () => new UserDefinedType(expr.Tok, datatypeDecl.Name, datatypeDecl, datatypeValue.InferredTypeArgs),
        ctor.Name));

    } else if (expr is ApplyExpr applyExpr) {
      flows.Add(new FlowFromTypeArgument(expr, applyExpr.Function.UnnormalizedType, applyExpr.Args.Count));

    } else if (expr is SetDisplayExpr setDisplayExpr) {
      foreach (var element in setDisplayExpr.Elements) {
        flows.Add(new FlowFromComputedTypeIgnoreHeadTypes(expr, () => new SetType(setDisplayExpr.Finite, TypeRefinementWrapper.NormalizeSansBottom(element)), "set display"));
      }

    } else if (expr is MultiSetDisplayExpr multiSetDisplayExpr) {
      foreach (var element in multiSetDisplayExpr.Elements) {
        flows.Add(new FlowFromComputedTypeIgnoreHeadTypes(expr, () => new MultiSetType(TypeRefinementWrapper.NormalizeSansBottom(element)), "multiset display"));
      }

    } else if (expr is SeqDisplayExpr seqDisplayExpr) {
      foreach (var element in seqDisplayExpr.Elements) {
        flows.Add(new FlowFromComputedTypeIgnoreHeadTypes(expr, () => new SeqType(TypeRefinementWrapper.NormalizeSansBottom(element)), "sequence display"));
      }

    } else if (expr is MapDisplayExpr mapDisplayExpr) {
      foreach (var element in mapDisplayExpr.Elements) {
        flows.Add(new FlowFromComputedTypeIgnoreHeadTypes(expr, () => new MapType(mapDisplayExpr.Finite,
            TypeRefinementWrapper.NormalizeSansBottom(element.A), TypeRefinementWrapper.NormalizeSansBottom(element.B)),
          "map display"));
      }

    } else if (expr is SetComprehension setComprehension) {
      flows.Add(new FlowFromComputedTypeIgnoreHeadTypes(expr,
        () => new SetType(setComprehension.Finite, TypeRefinementWrapper.NormalizeSansBottom(setComprehension.Term)),
        "set comprehension"));

    } else if (expr is MapComprehension mapComprehension) {
      flows.Add(new FlowFromComputedTypeIgnoreHeadTypes(expr, () => {
        Type keyType;
        if (mapComprehension.TermLeft != null) {
          keyType = TypeRefinementWrapper.NormalizeSansBottom(mapComprehension.TermLeft);
        } else {
          Contract.Assert(mapComprehension.BoundVars.Count == 1);
          keyType = TypeRefinementWrapper.NormalizeSansBottom(mapComprehension.BoundVars[0]);
        }
        return new MapType(mapComprehension.Finite, keyType, TypeRefinementWrapper.NormalizeSansBottom(mapComprehension.Term));
      }, "map comprehension"));

    } else if (expr is SeqConstructionExpr seqConstructionExpr) {
      flows.Add(new FlowFromComputedTypeIgnoreHeadTypes(expr,
        () => {
          var arrowType = (ArrowType)seqConstructionExpr.Initializer.Type.NormalizeToAncestorType();
          Contract.Assert(arrowType.TypeArgs.Count == 2);
          return new SeqType(TypeRefinementWrapper.NormalizeSansBottom(arrowType.TypeArgs[1]));
        },
        "seq constructor"));

    } else if (expr is BinaryExpr binaryExpr) {
      switch (binaryExpr.ResolvedOp) {
        case BinaryExpr.ResolvedOpcode.Iff:
        case BinaryExpr.ResolvedOpcode.Imp:
        case BinaryExpr.ResolvedOpcode.And:
        case BinaryExpr.ResolvedOpcode.Or:
        case BinaryExpr.ResolvedOpcode.Add:
        case BinaryExpr.ResolvedOpcode.Sub:
        case BinaryExpr.ResolvedOpcode.Mul:
        case BinaryExpr.ResolvedOpcode.Div:
        case BinaryExpr.ResolvedOpcode.Mod:
        case BinaryExpr.ResolvedOpcode.BitwiseAnd:
        case BinaryExpr.ResolvedOpcode.BitwiseOr:
        case BinaryExpr.ResolvedOpcode.BitwiseXor:
        case BinaryExpr.ResolvedOpcode.Union:
        case BinaryExpr.ResolvedOpcode.Intersection:
        case BinaryExpr.ResolvedOpcode.MultiSetUnion:
        case BinaryExpr.ResolvedOpcode.MultiSetIntersection:
        case BinaryExpr.ResolvedOpcode.Concat:
        case BinaryExpr.ResolvedOpcode.MapMerge:
          // For these operators, the result type is the same as that of E0 and E1.
          //
          // Note about intersection: In general, let set<C> be the result of combining the operands set<A> and set<B>
          // of intersection. To be precise, we would need C to be a type that conjoins the constraints of A and B.
          // We don't have such a time, so we instead (approximate the other direction and) let C be the join of A and B.
          flows.Add(new FlowBetweenExpressions(expr, binaryExpr.E0, BinaryExpr.OpcodeString(binaryExpr.Op)));
          flows.Add(new FlowBetweenExpressions(expr, binaryExpr.E1, BinaryExpr.OpcodeString(binaryExpr.Op)));
          break;
        case BinaryExpr.ResolvedOpcode.LeftShift:
        case BinaryExpr.ResolvedOpcode.RightShift:
        case BinaryExpr.ResolvedOpcode.SetDifference:
        case BinaryExpr.ResolvedOpcode.MultiSetDifference:
        case BinaryExpr.ResolvedOpcode.MapSubtraction:
          // For these operators, the result type is determined by E0.
          flows.Add(new FlowBetweenExpressions(expr, binaryExpr.E0, BinaryExpr.OpcodeString(binaryExpr.Op)));
          break;
        case BinaryExpr.ResolvedOpcode.EqCommon:
        case BinaryExpr.ResolvedOpcode.NeqCommon:
        case BinaryExpr.ResolvedOpcode.Lt:
        case BinaryExpr.ResolvedOpcode.Le:
        case BinaryExpr.ResolvedOpcode.Ge:
        case BinaryExpr.ResolvedOpcode.Gt:
        case BinaryExpr.ResolvedOpcode.LtChar:
        case BinaryExpr.ResolvedOpcode.LeChar:
        case BinaryExpr.ResolvedOpcode.GeChar:
        case BinaryExpr.ResolvedOpcode.GtChar:
        case BinaryExpr.ResolvedOpcode.SetEq:
        case BinaryExpr.ResolvedOpcode.SetNeq:
        case BinaryExpr.ResolvedOpcode.ProperSubset:
        case BinaryExpr.ResolvedOpcode.Subset:
        case BinaryExpr.ResolvedOpcode.Superset:
        case BinaryExpr.ResolvedOpcode.ProperSuperset:
        case BinaryExpr.ResolvedOpcode.Disjoint:
        case BinaryExpr.ResolvedOpcode.InSet:
        case BinaryExpr.ResolvedOpcode.NotInSet:
        case BinaryExpr.ResolvedOpcode.MultiSetEq:
        case BinaryExpr.ResolvedOpcode.MultiSetNeq:
        case BinaryExpr.ResolvedOpcode.MultiSubset:
        case BinaryExpr.ResolvedOpcode.MultiSuperset:
        case BinaryExpr.ResolvedOpcode.ProperMultiSubset:
        case BinaryExpr.ResolvedOpcode.ProperMultiSuperset:
        case BinaryExpr.ResolvedOpcode.MultiSetDisjoint:
        case BinaryExpr.ResolvedOpcode.InMultiSet:
        case BinaryExpr.ResolvedOpcode.NotInMultiSet:
        case BinaryExpr.ResolvedOpcode.SeqEq:
        case BinaryExpr.ResolvedOpcode.SeqNeq:
        case BinaryExpr.ResolvedOpcode.ProperPrefix:
        case BinaryExpr.ResolvedOpcode.Prefix:
        case BinaryExpr.ResolvedOpcode.InSeq:
        case BinaryExpr.ResolvedOpcode.NotInSeq:
        case BinaryExpr.ResolvedOpcode.MapEq:
        case BinaryExpr.ResolvedOpcode.MapNeq:
        case BinaryExpr.ResolvedOpcode.InMap:
        case BinaryExpr.ResolvedOpcode.NotInMap:
        case BinaryExpr.ResolvedOpcode.RankLt:
        case BinaryExpr.ResolvedOpcode.RankGt:
          // For these operators, the result type is fixed (to be bool), so there is no flow.
          break;
        case BinaryExpr.ResolvedOpcode.YetUndetermined:
        case BinaryExpr.ResolvedOpcode.LessThanLimit:
        default:
          Contract.Assert(false); // unexpected operator
          break;
      }

    } else if (expr is LetExpr letExpr) {
      if (letExpr.Exact) {
        Contract.Assert(letExpr.LHSs.Count == letExpr.RHSs.Count);
        for (var i = 0; i < letExpr.LHSs.Count; i++) {
          var rhs = letExpr.RHSs[i];
          VisitPattern(letExpr.LHSs[i], () => TypeRefinementWrapper.NormalizeSansBottom(rhs), context);
        }
      }
      flows.Add(new FlowBetweenExpressions(expr, letExpr.Body, "let"));

    } else if (expr is LambdaExpr lambdaExpr) {
      flows.Add(new FlowFromComputedType(expr, () => {
        return ModuleResolver.SelectAppropriateArrowType(lambdaExpr.Tok,
          lambdaExpr.BoundVars.ConvertAll(v => TypeRefinementWrapper.NormalizeSansBottom(v)),
          TypeRefinementWrapper.NormalizeSansBottom(lambdaExpr.Body),
          lambdaExpr.Reads.Expressions.Count != 0, lambdaExpr.Range != null, systemModuleManager);
      }, lambdaExpr.WhatKind));

    }

    base.PostVisitOneExpression(expr, context);
  }

  private void VisitPattern<VT>(CasePattern<VT> casePattern, Func<Type> getPatternRhsType, IASTVisitorContext context) where VT : class, IVariable {
    VisitExpression(casePattern.Expr, context);

    if (casePattern.Var != null) {
      flows.Add(new FlowIntoVariableFromComputedType(casePattern.Var, getPatternRhsType, casePattern.Tok, ":="));
      Contract.Assert(casePattern.Arguments == null);
    } else if (casePattern.Arguments != null) {
      var ctor = casePattern.Ctor;
      Contract.Assert(ctor != null);

      Func<Type> GetPatternArgumentType(int argumentIndex) {
        return () => {
          var sourceType = getPatternRhsType().NormalizeExpand();
          Contract.Assert(sourceType.IsDatatype);
          Contract.Assert(sourceType.TypeArgs.Count == ctor.EnclosingDatatype.TypeArgs.Count);
          var typeMap = TypeParameter.SubstitutionMap(ctor.EnclosingDatatype.TypeArgs, sourceType.TypeArgs);
          Contract.Assert(argumentIndex < ctor.Formals.Count);
          return ctor.Formals[argumentIndex].Type.Subst(typeMap);
        };
      }

      for (var i = 0; i < casePattern.Arguments.Count; i++) {
        VisitPattern<VT>(casePattern.Arguments[i], GetPatternArgumentType(i), context);
      }
    }

  }

  protected override void PostVisitOneStatement(Statement stmt, IASTVisitorContext context) {
    if (stmt is VarDeclPattern varDeclPattern) {
      VisitPattern(varDeclPattern.LHS, () => TypeRefinementWrapper.NormalizeSansBottom(varDeclPattern.RHS), context);
    } else if (stmt is SingleAssignStmt { Lhs: IdentifierExpr lhsIdentifierExpr } assignStmt) {
      if (assignStmt is { Rhs: ExprRhs exprRhs }) {
        flows.Add(new FlowIntoVariable(lhsIdentifierExpr.Var, exprRhs.Expr, assignStmt.Tok, ":="));
      } else if (assignStmt is { Rhs: TypeRhs tRhs }) {
        flows.Add(new FlowFromType(lhsIdentifierExpr.Var.UnnormalizedType, tRhs.Type, assignStmt.Tok, ":= new"));
      }

    } else if (stmt is AssignSuchThatStmt assignSuchThatStmt) {
      foreach (var lhs in assignSuchThatStmt.Lhss) {
        VisitExpression(lhs, context);
      }

    } else if (stmt is CallStmt callStmt) {
      Contract.Assert(callStmt.Args.Count == callStmt.Method.Ins.Count);
      for (var i = 0; i < callStmt.Args.Count; i++) {
        var formal = callStmt.Method.Ins[i];
        var actual = callStmt.Args[i];
        flows.Add(new FlowBetweenComputedTypes(() => {
          var typeMap = callStmt.MethodSelect.TypeArgumentSubstitutionsWithParents();
          return (TypeRefinementWrapper.NormalizeSansBottom(formal).Subst(typeMap), TypeRefinementWrapper.NormalizeSansBottom(actual));
        }, callStmt.Tok, $"{callStmt.Method.Name}({formal.Name} := ...)"));
      }

      Contract.Assert(callStmt.Lhs.Count == callStmt.Method.Outs.Count);
      for (var i = 0; i < callStmt.Lhs.Count; i++) {
        if (callStmt.Lhs[i] is IdentifierExpr actualIdentifierExpr) {
          var formal = callStmt.Method.Outs[i];
          flows.Add(new FlowIntoVariableFromComputedType(actualIdentifierExpr.Var, () => {
            var typeMap = callStmt.MethodSelect.TypeArgumentSubstitutionsWithParents();
            return TypeRefinementWrapper.NormalizeSansBottom(formal).Subst(typeMap);
          }, callStmt.Tok, $"{actualIdentifierExpr.Var.Name} := {callStmt.Method.Name}(...)"));
        }
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
#if SOON
          UpdateIfOmitted(idPattern.BoundVar.Type, idPattern.BoundVar.PreType);
#endif
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

  public void Solve(ErrorReporter reporter, bool debugPrint) {
    var context = new FlowContext(systemModuleManager, reporter, debugPrint);
    bool anythingChanged;
    do {
      anythingChanged = false;
      foreach (var flow in flows.Where(flow => !flow.HasError)) {
        anythingChanged |= flow.Update(context);
      }
    } while (anythingChanged);

    if (debugPrint) {
      DebugPrint();
    }
  }

}
