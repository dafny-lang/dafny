//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using JetBrains.Annotations;

namespace Microsoft.Dafny;


/// <summary>
/// The purpose of the PreTypeToTypeVisitor is to convert the final pre-types of the name-resolution/pre-type-inference
/// into types. The core method for doing the conversion is "PreType2Type". The rest of the class is concerned with
/// where name-resolution/pre-type-inference has come up with pre-types and where these are supposed to be written back
/// into the AST as types.
/// </summary>
class PreTypeToTypeVisitor : ASTVisitor<IASTVisitorContext> {
  public override IASTVisitorContext GetContext(IASTVisitorContext astVisitorContext, bool inFunctionPostcondition) {
    return astVisitorContext;
  }

  private readonly SystemModuleManager systemModuleManager;

  public PreTypeToTypeVisitor(SystemModuleManager systemModuleManager) {
    this.systemModuleManager = systemModuleManager;
  }

  private readonly List<(UpdatableTypeProxy, Type, string)> constraints = new();

  private void AddConstraint(UpdatableTypeProxy proxy, Type type, string description) {
    constraints.Add((proxy, type, description));
  }

  public void DebugPrint() {
    systemModuleManager.Options.OutputWriter.WriteLine("--------------------------- subset-type determination constraints:");
    foreach (var constraint in constraints) {
      var (proxy, type, description) = constraint;
      var bound = PreTypeConstraints.Pad($"%{proxy.UniqueId} :> {type}", 27);
      var value = PreTypeConstraints.Pad(proxy.currentValue == null ? "" : proxy.currentValue.ToString(), 20);
      systemModuleManager.Options.OutputWriter.WriteLine($"    {bound}  {value}    {description}");
    }
    systemModuleManager.Options.OutputWriter.WriteLine("------------------- (end of subset-type determination constraints)");
  }

  public void Solve(bool debugPrint) {
    bool anythingChanged;
    do {
      anythingChanged = false;
      foreach (var constraint in constraints) {
        var (proxy, type, _) = constraint;
        if (proxy.currentValue == null) {
          proxy.currentValue = type;
          anythingChanged = true;
        } else {
          var join = Type.Join(proxy.currentValue, type, systemModuleManager);
          if (!Type.Equal_Improved(proxy.currentValue, join)) {
            proxy.currentValue = join;
            anythingChanged = true;
          }
        }
      }
    } while (anythingChanged);

    if (debugPrint) {
      DebugPrint();
    }

    foreach (var constraint in constraints) {
      var proxy = constraint.Item1;
      if (proxy.currentValue != null) {
        proxy.T = proxy.currentValue;
      }
    }
  }

  public Type PreType2UpdatableType(PreType preType, Type lowerBound, string description) {
    var ty = PreType2TypeCore(preType, true);
    var proxy = new UpdatableTypeProxy(ty);
    AddConstraint(proxy, lowerBound, description);
    return proxy;
  }

  public static Type PreType2Type(PreType preType) {
    return PreType2TypeCore(preType, true);
  }

  public class UpdatableTypeProxy : TypeProxy {
    private static int count = 0;
    public readonly int UniqueId = count++;
    [CanBeNull] internal Type currentValue = null; // null stands for the unsatisfiable constraint (i.e., bottom)
    public UpdatableTypeProxy(Type ty) : base() {
      T = ty;
    }

    public override string TypeName(DafnyOptions options, ModuleDefinition context, bool parseAble) {
      var baseName = base.TypeName(options, context, parseAble);
      if (options.Get(CommonOptionBag.NewTypeInferenceDebug)) {
        return $"/*%{UniqueId}*/{baseName}";
      } else {
        return baseName;
      }
    }

    /// <summary>
    /// Normalize, but don't skip over any UpdatableTypeProxy
    /// </summary>
    public static Type NormalizeSansImprovementTypeProxy(Type ty) {
      while (ty is not UpdatableTypeProxy) {
        if (ty is TypeProxy { T: { } proxyFor }) {
          ty = proxyFor;
        } else {
          break;
        }
      }
      return ty;
    }

  }

  private static Type PreType2TypeCore(PreType preType, bool usePrintablePreType) {
    var pt = (DPreType)preType.Normalize(); // all pre-types should have been filled in and resolved to a non-proxy
    if (usePrintablePreType && pt.PrintablePreType != null) {
      pt = pt.PrintablePreType;
    }
    switch (pt.Decl.Name) {
      case "bool":
        return Type.Bool;
      case "char":
        return Type.Char;
      case "int":
        return Type.Int;
      case "real":
        return Type.Real;
      case "ORDINAL":
        return Type.BigOrdinal;
      case "set":
        return new SetType(true, PreType2Type(pt.Arguments[0]));
      case "iset":
        return new SetType(false, PreType2Type(pt.Arguments[0]));
      case "multiset":
        return new MultiSetType(PreType2Type(pt.Arguments[0]));
      case "seq":
        return new SeqType(PreType2Type(pt.Arguments[0]));
      case "map":
        return new MapType(true, PreType2Type(pt.Arguments[0]), PreType2Type(pt.Arguments[1]));
      case "imap":
        return new MapType(false, PreType2Type(pt.Arguments[0]), PreType2Type(pt.Arguments[1]));
      default:
        break;
    }
    var arguments = pt.Arguments.ConvertAll(ptArgument => PreType2Type(ptArgument));
    if (pt.Decl is ArrowTypeDecl arrowTypeDecl) {
      return new ArrowType(pt.Decl.tok, arrowTypeDecl, arguments);
    } else if (pt.Decl is ValuetypeDecl valuetypeDecl) {
      return valuetypeDecl.CreateType(arguments);
    } else if (pt.Decl is ClassLikeDecl { IsReferenceTypeDecl: true }) {
      return new UserDefinedType(pt.Decl.tok, pt.Decl.Name + "?", pt.Decl, arguments);
    } else {
      return new UserDefinedType(pt.Decl.tok, pt.Decl.Name, pt.Decl, arguments);
    }
  }

  public void VisitConstantsAndRedirectingTypes(List<TopLevelDecl> declarations) {
    foreach (var decl in declarations) {
      if (decl is NewtypeDecl newtypeDecl) {
        UpdateIfOmitted(newtypeDecl.BaseType, newtypeDecl.BasePreType);
      } else if (decl is SubsetTypeDecl subsetTypeDecl) {
        UpdateIfOmitted(subsetTypeDecl.Var.Type, subsetTypeDecl.Var.PreType);
      }
      if (decl is TopLevelDeclWithMembers topLevelDeclWithMembers) {
        foreach (var member in topLevelDeclWithMembers.Members.Where(member => member is ConstantField)) {
          var constField = (ConstantField)member;
          // The type of the const might have been omitted in the program text and then inferred
          UpdateIfOmitted(constField.Type, constField.PreType);
        }
      }
    }
  }

  private void UpdateIfOmitted(Type type, PreType preType, bool candidateForFutureSubsetImprovements = false) {
    var preTypeConverted = PreType2TypeCore(preType, false);
    if (candidateForFutureSubsetImprovements) {
      preTypeConverted = new UpdatableTypeProxy(preTypeConverted);
    }
    UpdateIfOmitted(type, preTypeConverted);
  }

  private void UpdateIfOmitted(Type type, Type preTypeConverted) {
    if (type is TypeProxy { T: null } typeProxy) {
      typeProxy.T = preTypeConverted;
    } else {
      type = type.NormalizeExpand();
      // TODO: "type" should also be moved up to the parent type that corresponds to "preType.Decl"
      var preTypeConvertedExpanded = preTypeConverted.NormalizeExpand();
      Contract.Assert((type as UserDefinedType)?.ResolvedClass == (preTypeConvertedExpanded as UserDefinedType)?.ResolvedClass);
      Contract.Assert(type.TypeArgs.Count == preTypeConvertedExpanded.TypeArgs.Count);
      if (preTypeConvertedExpanded.TypeArgs.Count != preTypeConverted.TypeArgs.Count) {
        Contract.Assert(true);
      }
      for (var i = 0; i < type.TypeArgs.Count; i++) {
        UpdateIfOmitted(type.TypeArgs[i], preTypeConvertedExpanded.TypeArgs[i]);
      }
    }
  }

  private void UpdateTypeOfVariables(IEnumerable<IVariable> variables, bool candidateForFutureSubsetImprovements = false) {
    foreach (var v in variables) {
      UpdateIfOmitted(v.Type, v.PreType, candidateForFutureSubsetImprovements);
    }
  }

  protected override void PostVisitOneExpression(Expression expr, IASTVisitorContext context) {
    if (expr is FunctionCallExpr functionCallExpr) {
      functionCallExpr.TypeApplication_AtEnclosingClass = functionCallExpr.PreTypeApplication_AtEnclosingClass.ConvertAll(PreType2Type);
      functionCallExpr.TypeApplication_JustFunction = functionCallExpr.PreTypeApplication_JustFunction.ConvertAll(PreType2Type);
    } else if (expr is MemberSelectExpr memberSelectExpr) {
      memberSelectExpr.TypeApplication_AtEnclosingClass = memberSelectExpr.PreTypeApplication_AtEnclosingClass.ConvertAll(PreType2Type);
      memberSelectExpr.TypeApplication_JustMember = memberSelectExpr.PreTypeApplication_JustMember.ConvertAll(PreType2Type);
    } else if (expr is ComprehensionExpr comprehensionExpr) {
      UpdateTypeOfVariables(comprehensionExpr.BoundVars);
    } else if (expr is LetExpr letExpr) {
      UpdateTypeOfVariables(letExpr.BoundVars, true);
      foreach (var lhs in letExpr.LHSs) {
        VisitPattern(lhs, context);
      }
    } else if (expr is DatatypeValue datatypeValue) {
      Contract.Assert(datatypeValue.InferredTypeArgs.Count == 0 || datatypeValue.InferredTypeArgs.Count == datatypeValue.InferredPreTypeArgs.Count);
      if (datatypeValue.InferredTypeArgs.Count == 0) {
        foreach (var preTypeArgument in datatypeValue.InferredPreTypeArgs) {
          datatypeValue.InferredTypeArgs.Add(PreType2Type(preTypeArgument));
        }
      }
    } else if (expr is ConversionExpr conversionExpr) {
      UpdateIfOmitted(conversionExpr.ToType, conversionExpr.PreType);
    }

    if (expr.PreType is UnusedPreType) {
      expr.Type = new InferredTypeProxy();
    } else if (expr is IdentifierExpr identifierExpr) {
      expr.UnnormalizedType = PreType2UpdatableType(expr.PreType, identifierExpr.Var.UnnormalizedType, identifierExpr.Name);
    } else {
      expr.Type = PreType2Type(expr.PreType);
    }
    base.PostVisitOneExpression(expr, context);

    if (expr is (not DefaultValueExpression) and ConcreteSyntaxExpression { ResolvedExpression: { } resolvedExpression }) {
      VisitExpression(resolvedExpression, context);
    }
  }

  private void VisitPattern<VT>(CasePattern<VT> casePattern, IASTVisitorContext context) where VT : class, IVariable {
    if (casePattern.Var != null) {
      UpdateIfOmitted(casePattern.Var.Type, casePattern.Var.PreType);
    }
    VisitExpression(casePattern.Expr, context);

    if (casePattern.Arguments != null) {
      casePattern.Arguments.ForEach(v => VisitPattern(v, context));
    }
  }

  protected override bool VisitOneStatement(Statement stmt, IASTVisitorContext context) {
    if (stmt is VarDeclStmt varDeclStmt) {
      UpdateTypeOfVariables(varDeclStmt.Locals, true);
    } else if (stmt is VarDeclPattern varDeclPattern) {
      UpdateTypeOfVariables(varDeclPattern.LocalVars, true);
    } else if (stmt is ForallStmt forallStmt) {
      UpdateTypeOfVariables(forallStmt.BoundVars);
    }

    return base.VisitOneStatement(stmt, context);
  }

  protected override void PostVisitOneStatement(Statement stmt, IASTVisitorContext context) {
    if (stmt is VarDeclPattern varDeclPattern) {
      VisitPattern(varDeclPattern.LHS, context);
    } else if (stmt is AssignStmt assignStmt) {
      Type rhsType = null;
      string rhsDescription = "";
      if (assignStmt is { Rhs: ExprRhs exprRhs }) {
        rhsType = exprRhs.Expr.Resolved.UnnormalizedType;
      } else if (assignStmt is { Rhs: TypeRhs tRhs }) {
        tRhs.Type = PreType2Type(tRhs.PreType);
        if (tRhs.ArrayDimensions != null) {
          // In this case, we expect tRhs.PreType to be an array type
          var arrayPreType = (DPreType)tRhs.PreType.Normalize();
          Contract.Assert(arrayPreType.Decl is ArrayClassDecl);
          Contract.Assert(arrayPreType.Arguments.Count == 1);
          UpdateIfOmitted(tRhs.EType, arrayPreType.Arguments[0]);
        } else {
          UpdateIfOmitted(tRhs.EType, tRhs.PreType);
        }
        rhsType = tRhs.EType;
        rhsDescription = " new";
      }

      if (assignStmt.Lhs is IdentifierExpr lhsIdentifierExpr) {
        if (UpdatableTypeProxy.NormalizeSansImprovementTypeProxy(lhsIdentifierExpr.Var.UnnormalizedType) is UpdatableTypeProxy updatableTypeProxy) {
          AddConstraint(updatableTypeProxy, rhsType, $"{lhsIdentifierExpr.Var.Name} :={rhsDescription}");
        }
      }

    } else if (stmt is AssignSuchThatStmt assignSuchThatStmt) {
      foreach (var lhs in assignSuchThatStmt.Lhss) {
        VisitExpression(lhs, context);
      }

    } else if (stmt is CallStmt callStmt) {
      var typeSubst = callStmt.MethodSelect.TypeArgumentSubstitutionsWithParents();
      Contract.Assert(callStmt.Lhs.Count == callStmt.Method.Outs.Count);
      for (var i = 0; i < callStmt.Lhs.Count; i++) {
        if (callStmt.Lhs[i] is IdentifierExpr lhsIdentifierExpr) {
          if (UpdatableTypeProxy.NormalizeSansImprovementTypeProxy(lhsIdentifierExpr.Var.UnnormalizedType) is UpdatableTypeProxy updatableTypeProxy) {
            var formal = callStmt.Method.Outs[i];
            AddConstraint(updatableTypeProxy, formal.Type.Subst(typeSubst), $"{lhsIdentifierExpr.Var.Name} := call {callStmt.Method.Name}");
          }
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
    } else if (stmt is ForLoopStmt forLoopStmt) {
      UpdateIfOmitted(forLoopStmt.LoopIndex.Type, forLoopStmt.LoopIndex.PreType);
    }

    base.PostVisitOneStatement(stmt, context);

    if (stmt is UpdateStmt updateStmt) {
      foreach (var ss in updateStmt.ResolvedStatements) {
        VisitStatement(ss, context);
      }
    }
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
          UpdateIfOmitted(idPattern.BoundVar.Type, idPattern.BoundVar.PreType);
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
