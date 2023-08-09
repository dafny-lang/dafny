//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

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

  private void AddConstraint(UpdatableTypeProxy proxy, Type type, string description, IToken tok) {
    constraints.Add((proxy, type, $"({tok.line},{tok.col}) {description}"));
  }

  public void DebugPrint() {
    systemModuleManager.Options.OutputWriter.WriteLine($"--------------------------- subset-type determination constraints:");
    foreach (var constraint in constraints) {
      var (proxy, type, description) = constraint;
      var bound = PreTypeConstraints.Pad($"%{proxy.UniqueId} :> {UpdatableTypeProxy.ToStringAsUpdatableTypeProxy(type)}", 27);
      var value = PreTypeConstraints.Pad(UpdatableTypeProxy.ToStringAsBottom(proxy), 20);
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
        var join = Join(proxy, type);
        if ((proxy.IsBottomType && !UpdatableTypeProxy.NormalizesToBottom(join)) || !Type.Equal_Improved(proxy, join)) {
          if (debugPrint) {
            systemModuleManager.Options.OutputWriter.WriteLine(
              $"DEBUG: updating proxy %{proxy.UniqueId} to {UpdatableTypeProxy.ToStringAsUpdatableTypeProxy(type)}" +
              $" ({UpdatableTypeProxy.ToStringAsBottom(proxy)} \\/ {UpdatableTypeProxy.ToStringAsBottom(type)})");
          }
          proxy.T = join;
          anythingChanged = true;
        }
      }
    } while (anythingChanged);

    if (debugPrint) {
      DebugPrint();
    }

    foreach (var constraint in constraints) {
      var proxy = constraint.Item1;
      if (proxy.IsBottomType) {
        proxy.T = proxy.Normalize();
      }
    }
  }

  public UpdatableTypeProxy PreType2UpdatableType(PreType preType, Type lowerBound, string description, IToken tok) {
    var ty = PreType2TypeCore(preType, true);
    var proxy = new UpdatableTypeProxy(ty);
    AddConstraint(proxy, lowerBound, $"{description}", tok);
    return proxy;
  }

  public UpdatableTypeProxy PreType2UpdatableType(PreType preType) {
    var ty = PreType2TypeCore(preType, true);
    var proxy = new UpdatableTypeProxy(ty);
    return proxy;
  }

  public static Type PreType2Type(PreType preType) {
    return PreType2TypeCore(preType, true);
  }

  public class BottomTypePlaceholder : TypeProxy {
    public BottomTypePlaceholder(Type baseType) {
      T = baseType;
    }
  }

  public class UpdatableTypeProxy : TypeProxy {
    private static int count = 0;
    public readonly int UniqueId = count++;
    public UpdatableTypeProxy(Type type) : base() {
      T = new BottomTypePlaceholder(type);
    }

    public bool IsBottomType => T is BottomTypePlaceholder;

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

    public static string ToStringAsUpdatableTypeProxy(Type type) {
      type = NormalizeSansImprovementTypeProxy(type);
      if (type is UpdatableTypeProxy utp) {
        return $"%{utp.UniqueId}";
      } else {
        return type.ToString();
      }
    }

    public static string ToStringAsBottom(Type type) {
      type = NormalizeSansImprovementTypeProxy(type);
      if (type is UpdatableTypeProxy { IsBottomType: true}) {
        return "\\bot";
      } else {
        return type.ToString();
      }
    }

    public static bool NormalizesToBottom(Type type) {
      while (true) {
        type = NormalizeSansImprovementTypeProxy(type);
        if (type is UpdatableTypeProxy updatableTypeProxy) {
          if (updatableTypeProxy.IsBottomType) {
            return true;
          }
          type = updatableTypeProxy.T;
        } else {
          return false;
        }
      }
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
    var arguments = pt.Arguments.ConvertAll(PreType2Type);
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
      preTypeConverted = preTypeConverted.NormalizeExpand();
      Contract.Assert((type as UserDefinedType)?.ResolvedClass == (preTypeConverted as UserDefinedType)?.ResolvedClass);
      Contract.Assert(type.TypeArgs.Count == preTypeConverted.TypeArgs.Count);
      for (var i = 0; i < type.TypeArgs.Count; i++) {
        UpdateIfOmitted(type.TypeArgs[i], preTypeConverted.TypeArgs[i]);
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
      expr.UnnormalizedType = PreType2UpdatableType(expr.PreType, identifierExpr.Var.UnnormalizedType, identifierExpr.Name, identifierExpr.tok);
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
    } else if (expr is ITEExpr iteExpr) {
      var proxy = PreType2UpdatableType(expr.PreType);
      expr.UnnormalizedType = proxy;
      AddConstraint(proxy, iteExpr.Thn.UnnormalizedType, "if-then", iteExpr.tok);
      AddConstraint(proxy, iteExpr.Els.UnnormalizedType, "if-else", iteExpr.tok);
    } else if (expr is ConcreteSyntaxExpression { ResolvedExpression: { } resolvedExpression }) {
      expr.UnnormalizedType = resolvedExpression.UnnormalizedType;
    } else {
      expr.Type = PreType2Type(expr.PreType);
    }
    base.PostVisitOneExpression(expr, context);
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
        // convert the type of the RHS, which we expect to be a reference type, and then create the non-null version of it
        var udtConvertedFromPretype = (UserDefinedType)PreType2Type(tRhs.PreType);
        Contract.Assert(udtConvertedFromPretype.IsRefType);
        tRhs.Type = UserDefinedType.CreateNonNullType(udtConvertedFromPretype);
        if (tRhs.ArrayDimensions != null) {
          // In this case, we expect tRhs.PreType to be an array type
          var arrayPreType = (DPreType)tRhs.PreType.Normalize();
          Contract.Assert(arrayPreType.Decl is ArrayClassDecl);
          Contract.Assert(arrayPreType.Arguments.Count == 1);
          UpdateIfOmitted(tRhs.EType, arrayPreType.Arguments[0]);
        } else {
          UpdateIfOmitted(tRhs.EType, tRhs.Type);
        }
        rhsType = tRhs.Type;
        rhsDescription = " new";
      }

      if (assignStmt.Lhs is IdentifierExpr lhsIdentifierExpr) {
        if (UpdatableTypeProxy.NormalizeSansImprovementTypeProxy(lhsIdentifierExpr.Var.UnnormalizedType) is UpdatableTypeProxy updatableTypeProxy) {
          AddConstraint(updatableTypeProxy, rhsType, $"{lhsIdentifierExpr.Var.Name} :={rhsDescription}", assignStmt.tok);
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
            AddConstraint(updatableTypeProxy, formal.Type.Subst(typeSubst), $"{lhsIdentifierExpr.Var.Name} := call {callStmt.Method.Name}", callStmt.tok);
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
    } else if (stmt is ForallStmt forallStmt) {
      UpdateTypeOfVariables(forallStmt.BoundVars);
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

  /// <summary>
  /// Does a best-effort to compute the join of "a" and "b", where the base types of "a" and "b" (or
  /// some parent type thereof) are the same.
  /// If there is no join (for example, if type parameters in a non-variant position are
  /// incompatible), then use base types as such type arguments.
  /// </summary>
  public Type Join(Type a, Type b) {
    Contract.Requires(a != null);
    Contract.Requires(b != null);

    if (a is UpdatableTypeProxy { IsBottomType: true }) {
      return b;
    } else if (b is UpdatableTypeProxy { IsBottomType: true }) {
      return a;
    }

    // As a special-case optimization, check for equality here
    if (a.Equals(b, true)) {
      return a;
    }

    // Before we do anything else, make a note of whether or not both "a" and "b" are non-null types.
    var abNonNullTypes = a.IsNonNullRefType && b.IsNonNullRefType;

    var towerA = Type.GetTowerOfSubsetTypes(a);
    var towerB = Type.GetTowerOfSubsetTypes(b);
    // We almost expect the base types of these towers to be the same, since the module has successfully gone through pre-resolution and the
    // pre-resolution underspecification checks. However, there are considerations.
    //   - One is that the two given types may contain unused type parameters in type synonyms or subset types, and pre-resolution does not
    //     fill those in or detect their absence.
    //   - The other is traits.
    for (var n = System.Math.Min(towerA.Count, towerB.Count); 1 <= --n;) {
      a = towerA[n];
      b = towerB[n];
      var udtA = (UserDefinedType)a;
      var udtB = (UserDefinedType)b;
      if (udtA.ResolvedClass == udtB.ResolvedClass) {
        // We have two subset types with equal heads
        if (a.Equals(b, true)) { // optimization for a special case, which applies for example when there are no arguments or when the types happen to be the same
          return a;
        }
        Contract.Assert(a.TypeArgs.Count == b.TypeArgs.Count);
        var typeArgs = Joins(TypeParameter.Variances(udtA.ResolvedClass.TypeArgs), a.TypeArgs, b.TypeArgs);
        return new UserDefinedType(udtA.tok, udtA.Name, udtA.ResolvedClass, typeArgs);
      }
    }
    // We exhausted all possibilities of subset types being equal, so use the base-most types.
    a = towerA[0];
    b = towerB[0];

    if (a is BasicType) {
      Contract.Assert(b is BasicType);
      Contract.Assert(a.Equals(b, true));
      return a;

    } else if (a is CollectionType) {
      var directions = a.TypeArgs.ConvertAll(_ => TypeParameter.TPVariance.Co);
      var typeArgs = Joins(directions, a.TypeArgs, b.TypeArgs);
      Contract.Assert(typeArgs.Count == (a is MapType ? 2 : 1));
      if (a is SetType aSetType) {
        var bSetType = (SetType)b;
        Contract.Assert(aSetType.Finite == bSetType.Finite);
        return new SetType(aSetType.Finite, typeArgs[0]);
      } else if (a is MultiSetType) {
        Contract.Assert(b is MultiSetType);
        return new MultiSetType(typeArgs[0]);
      } else if (a is SeqType) {
        Contract.Assert(b is SeqType);
        return new SeqType(typeArgs[0]);
      } else {
        var aMapType = (MapType)a;
        var bMapType = (MapType)b;
        Contract.Assert(aMapType.Finite == bMapType.Finite);
        return new MapType(aMapType.Finite, typeArgs[0], typeArgs[1]);
      }

    } else if (a.AsArrowType != null) {
      ArrowType aa = a.AsArrowType;
      var bb = b.AsArrowType;
      Contract.Assert(aa != null && bb != null && aa.Arity == bb.Arity);
      int arity = aa.Arity;
      Contract.Assert(a.TypeArgs.Count == arity + 1);
      Contract.Assert(b.TypeArgs.Count == arity + 1);
      Contract.Assert(aa.ResolvedClass == bb.ResolvedClass);
      var typeArgs = Joins(aa.Variances(), a.TypeArgs, b.TypeArgs);
      return new ArrowType(aa.tok, (ArrowTypeDecl)aa.ResolvedClass, typeArgs);
    }

    // Convert a and b to their common supertype
    var aDecl = (TopLevelDeclWithMembers)((UserDefinedType)a).ResolvedClass;
    var bDecl = (TopLevelDeclWithMembers)((UserDefinedType)b).ResolvedClass;
    var commonSupertypeDecl = PreTypeConstraints.JoinHeads(aDecl, bDecl, systemModuleManager);
    Contract.Assert(commonSupertypeDecl != null);
    var aTypeSubstMap = TypeParameter.SubstitutionMap(aDecl.TypeArgs, a.TypeArgs);
    aDecl.AddParentTypeParameterSubstitutions(aTypeSubstMap);
    var bTypeSubstMap = TypeParameter.SubstitutionMap(bDecl.TypeArgs, b.TypeArgs);
    bDecl.AddParentTypeParameterSubstitutions(bTypeSubstMap);

    a = UserDefinedType.FromTopLevelDecl(commonSupertypeDecl.tok, commonSupertypeDecl).Subst(aTypeSubstMap);
    b = UserDefinedType.FromTopLevelDecl(commonSupertypeDecl.tok, commonSupertypeDecl).Subst(bTypeSubstMap);

    var joinedTypeArgs = Joins(TypeParameter.Variances(commonSupertypeDecl.TypeArgs), a.TypeArgs, b.TypeArgs);
    var udt = (UserDefinedType)a;
    var result = new UserDefinedType(udt.tok, udt.Name, commonSupertypeDecl, joinedTypeArgs);
    return abNonNullTypes && result.IsRefType ? UserDefinedType.CreateNonNullType(result) : result;
  }

  /// <summary>
  /// Does a best-effort to compute the meet of "a" and "b", where the base types of "a" and "b" (or
  /// some parent type thereof) are the same.
  /// If there is no meet (for example, if type parameters in a non-variant position are
  /// incompatible), then use a bottom type for the common base types of "a" and "b".
  /// </summary>
  public Type Meet(Type a, Type b) {
    Contract.Requires(a != null);
    Contract.Requires(b != null);

    // a crude implementation for now
    if (Type.IsSupertype(a, b)) {
      return b;
    } else if (Type.IsSupertype(b, a)) {
      return a;
    } else {
      // TODO: the following may not be correct in the face of traits
      return new BottomTypePlaceholder(a.NormalizeExpand());
    }
  }

  /// <summary>
  /// For each i, compute some combination of a[i] and b[i], according to direction[i].
  /// For a Co direction, use Join(a[i], b[i]).
  /// For a Contra direction (Co), use Meet(a[i], b[i]).
  /// For a Non direction, use a[i], provided a[i] and b[i] are equal, or otherwise use the base type of a[i].
  /// </summary>
  public List<Type> Joins(List<TypeParameter.TPVariance> directions, List<Type> a, List<Type> b) {
    Contract.Requires(directions != null);
    Contract.Requires(a != null);
    Contract.Requires(b != null);
    Contract.Requires(directions.Count == a.Count);
    Contract.Requires(directions.Count == b.Count);

    var count = directions.Count;
    var extrema = new List<Type>(count);
    for (var i = 0; i < count; i++) {
      Type output;
      if (directions[i] == TypeParameter.TPVariance.Co) {
        output = Join(a[i], b[i]);
      } else if (directions[i] == TypeParameter.TPVariance.Contra) {
        output = Meet(a[i], b[i]);
      } else {
        Contract.Assert(directions[i] == TypeParameter.TPVariance.Non);
        if (UpdatableTypeProxy.NormalizesToBottom(a[i])) {
          output = b[i];
        } else if (UpdatableTypeProxy.NormalizesToBottom(b[i])) {
          output = a[i];
        } else if (a[i].Equals(b[i], true)) {
          output = a[i];
        } else {
          // use the base type
          output = a[i].NormalizeExpand();
        }
      }
      extrema.Add(output);
    }
    return extrema;
  }

}
