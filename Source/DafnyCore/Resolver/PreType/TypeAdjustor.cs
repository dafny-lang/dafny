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
    systemModuleManager.Options.OutputWriter.WriteLine($"--------------------------- type-adjustment flows:");
    foreach (var flow in flows) {
      flow.DebugPrint(systemModuleManager.Options.OutputWriter);
    }
    systemModuleManager.Options.OutputWriter.WriteLine("------------------- (end of type-adjustment flows)");
  }

  protected override void PostVisitOneExpression(Expression expr, IASTVisitorContext context) {
    if (expr is IdentifierExpr identifierExpr) {
      flows.Add(new FlowFromType(expr, identifierExpr.Var.UnnormalizedType, identifierExpr.Name));

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
      Contract.Assert(functionCallExpr.Args.Count == functionCallExpr.Function.Formals.Count);
      for (var i = 0; i < functionCallExpr.Args.Count; i++) {
        var formal = functionCallExpr.Function.Formals[i];
        var actual = functionCallExpr.Args[i];
        flows.Add(new FlowBetweenComputedTypes(() => {
          var typeMap = functionCallExpr.TypeArgumentSubstitutionsWithParents();
          return (formal.Type.Subst(typeMap), actual.Type);
        }, functionCallExpr.tok, $"{functionCallExpr.Function.Name}({formal.Name} := ...)"));
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
          return (formal.Type.Subst(typeMap), actual.Type);
        }, datatypeValue.tok, $"{ctor.Name}({formal.Name} := ...)"));
      }
      flows.Add(new FlowFromComputedType(expr,
        () => new UserDefinedType(expr.tok, datatypeDecl.Name, datatypeDecl, datatypeValue.InferredTypeArgs),
        ctor.Name));

    } else if (expr is ApplyExpr applyExpr) {
      flows.Add(new FlowFromTypeArgument(expr, applyExpr.Function.UnnormalizedType, applyExpr.Args.Count));

    } else if (expr is SetDisplayExpr setDisplayExpr) {
      foreach (var element in setDisplayExpr.Elements) {
        flows.Add(new FlowFromComputedType(expr, () => new SetType(setDisplayExpr.Finite, element.Type), "set display"));
      }

    } else if (expr is MultiSetDisplayExpr multiSetDisplayExpr) {
      foreach (var element in multiSetDisplayExpr.Elements) {
        flows.Add(new FlowFromComputedType(expr, () => new MultiSetType(element.Type), "multiset display"));
      }

    } else if (expr is SeqDisplayExpr seqDisplayExpr) {
      foreach (var element in seqDisplayExpr.Elements) {
        flows.Add(new FlowFromComputedType(expr, () => new SeqType(element.Type), "sequence display"));
      }

    } else if (expr is MapDisplayExpr mapDisplayExpr) {
      foreach (var element in mapDisplayExpr.Elements) {
        flows.Add(new FlowFromComputedType(expr, () => new MapType(mapDisplayExpr.Finite, element.A.Type, element.B.Type),
          "map display"));
      }

    } else if (expr is BinaryExpr binaryExpr) {
      switch (binaryExpr.ResolvedOp) {
        case BinaryExpr.ResolvedOpcode.Union:
        case BinaryExpr.ResolvedOpcode.MultiSetUnion:
        case BinaryExpr.ResolvedOpcode.Concat:
        case BinaryExpr.ResolvedOpcode.MapMerge:
        case BinaryExpr.ResolvedOpcode.Intersection:
        case BinaryExpr.ResolvedOpcode.MultiSetIntersection:
          // Note about intersection: In general, let set<C> be the result of combining the operands set<A> and set<B>
          // of intersection. To be precise, we would need C to be a type that conjoins the constraints of A and B.
          // We don't have such a time, so we instead (approximate the other direction and) let C be the join of A and B.
          flows.Add(new FlowBetweenExpressions(expr, binaryExpr.E0, BinaryExpr.OpcodeString(binaryExpr.Op)));
          flows.Add(new FlowBetweenExpressions(expr, binaryExpr.E1, BinaryExpr.OpcodeString(binaryExpr.Op)));
          break;
        case BinaryExpr.ResolvedOpcode.SetDifference:
        case BinaryExpr.ResolvedOpcode.MultiSetDifference:
        case BinaryExpr.ResolvedOpcode.MapSubtraction:
          flows.Add(new FlowBetweenExpressions(expr, binaryExpr.E0, BinaryExpr.OpcodeString(binaryExpr.Op)));
          break;
        default:
          break;
      }
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
      if (assignStmt is { Rhs: ExprRhs exprRhs }) {
        flows.Add(new FlowIntoVariable(lhsIdentifierExpr.Var, exprRhs.Expr, assignStmt.tok, ":="));
      } else if (assignStmt is { Rhs: TypeRhs tRhs }) {
        flows.Add(new FlowFromType(lhsIdentifierExpr.Var.UnnormalizedType, tRhs.Type, assignStmt.tok, ":= new"));
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
          return (formal.Type.Subst(typeMap), actual.Type);
        }, callStmt.tok, $"{callStmt.Method.Name}({formal.Name} := ...)"));
      }

      Contract.Assert(callStmt.Lhs.Count == callStmt.Method.Outs.Count);
      for (var i = 0; i < callStmt.Lhs.Count; i++) {
        if (callStmt.Lhs[i] is IdentifierExpr actualIdentifierExpr) {
          var formal = callStmt.Method.Outs[i];
          flows.Add(new FlowIntoVariableFromComputedType(actualIdentifierExpr.Var, () => {
            var typeMap = callStmt.MethodSelect.TypeArgumentSubstitutionsWithParents();
            return formal.Type.Subst(typeMap);
          }, callStmt.tok, $"{actualIdentifierExpr.Var.Name} := {callStmt.Method.Name}(...)"));
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
