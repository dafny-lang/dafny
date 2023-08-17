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
/// The purpose of the TypeAdjustorVisitor is to incorporate subset types into the types that were inferred during
/// pre-type inference. The visitor collects constraints, which are solved by the Solve() method.
/// </summary>
public class TypeAdjustorVisitor : ASTVisitor<IASTVisitorContext> {
  public override IASTVisitorContext GetContext(IASTVisitorContext astVisitorContext, bool inFunctionPostcondition) {
    return astVisitorContext;
  }

  private readonly SystemModuleManager systemModuleManager;

  public TypeAdjustorVisitor(SystemModuleManager systemModuleManager) {
    this.systemModuleManager = systemModuleManager;
  }

  private readonly List<Flow> flows = new();

  public void DebugPrint() {
    systemModuleManager.Options.OutputWriter.WriteLine($"--------------------------- subset-type determination flows:");
    foreach (var flow in flows) {
      flow.DebugPrint(systemModuleManager.Options.OutputWriter);
    }
    systemModuleManager.Options.OutputWriter.WriteLine("------------------- (end of subset-type determination flows)");
  }

  protected override void PostVisitOneExpression(Expression expr, IASTVisitorContext context) {
    if (expr is IdentifierExpr identifierExpr) {
      flows.Add(new FlowFromType(expr, identifierExpr.Var.UnnormalizedType));

    } else if (expr is SeqSelectExpr selectExpr) {
      var seqType = selectExpr.Seq.UnnormalizedType;
      if (!selectExpr.SelectOne) {
        flows.Add(new FlowFromComputedType(expr, () => new SeqType(seqType.NormalizeExpand().TypeArgs[0])));
      } else if (seqType.AsSeqType != null || seqType.IsArrayType) {
        flows.Add(new FlowFromTypeArgument(expr, seqType, 0));
      } else if (seqType.IsMapType || seqType.IsIMapType) {
        flows.Add(new FlowFromTypeArgument(expr, seqType, 1));
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
#if SOON
    } else if (expr is MemberSelectExpr memberSelectExpr) {
      var typeMap = memberSelectExpr.TypeArgumentSubstitutionsWithParents();
      Type memberType;
      if (memberSelectExpr.Member is Field field) {
        memberType = field.Type.Subst(typeMap);
      } else {
        var function = (Function)memberSelectExpr.Member;
        memberType = ModuleResolver.SelectAppropriateArrowTypeForFunction(function, typeMap, systemModuleManager);
      }
      expr.UnnormalizedType = PreType2UpdatableType(expr.PreType, memberType, $".{memberSelectExpr.MemberName}", memberSelectExpr.tok);
    } else {
      expr.Type = PreType2Type(expr.PreType);
#endif
    }
    base.PostVisitOneExpression(expr, context);
  }

  private void VisitPattern<VT>(CasePattern<VT> casePattern, IASTVisitorContext context) where VT : class, IVariable {
    VisitExpression(casePattern.Expr, context);

    if (casePattern.Arguments != null) {
      casePattern.Arguments.ForEach(v => VisitPattern(v, context));
    }
  }

  protected override void PostVisitOneStatement(Statement stmt, IASTVisitorContext context) {
    if (stmt is VarDeclPattern varDeclPattern) {
      VisitPattern(varDeclPattern.LHS, context);
    } else if (stmt is AssignStmt { Lhs: IdentifierExpr lhsIdentifierExpr } assignStmt) {
      if (AdjustableType.NormalizeSansAdjustableType(lhsIdentifierExpr.Var.UnnormalizedType) is AdjustableType) {
        if (assignStmt is { Rhs: ExprRhs exprRhs }) {
          flows.Add(new FlowIntoVariable(lhsIdentifierExpr.Var, exprRhs.Expr, assignStmt.tok, ":="));
        } else if (assignStmt is { Rhs: TypeRhs tRhs }) {
          flows.Add(new FlowFromType(lhsIdentifierExpr.Var.UnnormalizedType, tRhs.Type, assignStmt.tok, ":= new"));
        }
      }

    } else if (stmt is AssignSuchThatStmt assignSuchThatStmt) {
      foreach (var lhs in assignSuchThatStmt.Lhss) {
        VisitExpression(lhs, context);
      }

    } else if (stmt is CallStmt callStmt) {
      var typeSubst = callStmt.MethodSelect.TypeArgumentSubstitutionsWithParents();
      Contract.Assert(callStmt.Lhs.Count == callStmt.Method.Outs.Count);
#if SOON
      for (var i = 0; i < callStmt.Lhs.Count; i++) {
        if (callStmt.Lhs[i] is IdentifierExpr lhsIdentifierExpr) {
          if (AdjustableType.NormalizeSansAdjustableType(lhsIdentifierExpr.Var.UnnormalizedType) is AdjustableType updatableTypeProxy) {
            var formal = callStmt.Method.Outs[i];
            AddConstraint(updatableTypeProxy, formal.Type.Subst(typeSubst), $"{lhsIdentifierExpr.Var.Name} := call {callStmt.Method.Name}", callStmt.tok);
          }
        }
      }
#endif

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
      foreach (var flow in flows) {
        anythingChanged |= flow.Update(context);
      }
    } while (anythingChanged);

    if (debugPrint) {
      DebugPrint();
    }
  }

}
