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

  public Type PreType2UpdatableType(PreType preType, Type lowerBound, string description, IToken tok) {
    var ty = PreType2TypeCore(preType, true);
    var proxy = new UpdatableTypeProxy(ty);
    AddConstraint(proxy, lowerBound, $"{description}", tok);
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
      expr.UnnormalizedType = PreType2UpdatableType(expr.PreType, identifierExpr.Var.UnnormalizedType, identifierExpr.Name, identifierExpr.tok);
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

  /// <summary>
  /// Does a best-effort to compute the join of "a" and "b", where the base types of "a" and "b" are
  /// the same. If there is no join (for example, if type parameters in a non-variant position are
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
    // We expect the base types of these towers to be the same, since the module has successfully gone through pre-resolution and the
    // pre-resolution underspecification checks. However, there are considerations.
    //   - One is that the two given types may contain unused type parameters in type synonyms or subset types, and pre-resolution does not
    //     fill those in or detect their absence. But the base of the towers will still be the same, because the .Equals method expand through
    //     those types.
    //   - The other is traits. TODO
    Contract.Assert(towerA[0].Equals(towerB[0])); // TODO: this is true until we start considering traits as well (see comment above)
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

    } else if (b.IsObjectQ) {
      var udtB = (UserDefinedType)b;
      return !a.IsRefType ? null : abNonNullTypes ? UserDefinedType.CreateNonNullType(udtB) : udtB;
    } else if (a.IsObjectQ) {
      var udtA = (UserDefinedType)a;
      return !b.IsRefType ? null : abNonNullTypes ? UserDefinedType.CreateNonNullType(udtA) : udtA;

    } else if (a.Equals(b, true)) {
      // this is an optimization for a special case, which applies for example when there are no arguments or when the types happen to be the same
      return a;

    } else {
      var aa = ((UserDefinedType)a).ResolvedClass;
      var bb = ((UserDefinedType)b).ResolvedClass;

      if (aa == bb) {
        Contract.Assert(a.TypeArgs.Count == b.TypeArgs.Count);
        var typeArgs = Joins(TypeParameter.Variances(aa.TypeArgs), a.TypeArgs, b.TypeArgs);
        var udt = (UserDefinedType)a;
        var result = new UserDefinedType(udt.tok, udt.Name, aa, typeArgs);
        return abNonNullTypes ? UserDefinedType.CreateNonNullType(result) : result;
      } else {
        Contract.Assert(false); // TODO: this assertion holds until traits are considered

        var A = (TopLevelDeclWithMembers)aa;
        var B = (TopLevelDeclWithMembers)bb;
        if (A.HeadDerivesFrom(B)) {
          var udtB = (UserDefinedType)b;
          return abNonNullTypes ? UserDefinedType.CreateNonNullType(udtB) : udtB;
        } else if (B.HeadDerivesFrom(A)) {
          var udtA = (UserDefinedType)a;
          return abNonNullTypes ? UserDefinedType.CreateNonNullType(udtA) : udtA;
        }
        // A and B are classes or traits. They always have object as a common supertype, but they may also both be extending some other
        // trait.  If such a trait is unique, pick it. (Unfortunately, this makes the join operation not associative.)
        var commonTraits = TopLevelDeclWithMembers.CommonTraits(A, B);
        if (commonTraits.Count == 1) {
          var typeMap = TypeParameter.SubstitutionMap(A.TypeArgs, a.TypeArgs);
          var r = (UserDefinedType)commonTraits[0].Subst(typeMap);
          return abNonNullTypes ? UserDefinedType.CreateNonNullType(r) : r;
        } else {
          // the unfortunate part is when commonTraits.Count > 1 here :(
          return abNonNullTypes ? UserDefinedType.CreateNonNullType(systemModuleManager.ObjectQ()) : systemModuleManager.ObjectQ();
        }
      }
    }
  }

  /// <summary>
  /// Does a best-effort to compute the meet of "a" and "b", returning "null" if not successful.
  ///
  /// Since some type parameters may still be proxies, it could be that the returned type is not
  /// really a meet, so the caller should set up additional constraints that the result is
  /// assignable to both a and b.
  /// </summary>
  public Type Meet(Type a, Type b) {
    Contract.Requires(a != null);
    Contract.Requires(b != null);

    a = a.NormalizeExpandKeepConstraints();
    b = b.NormalizeExpandKeepConstraints();

    var joinNeedsNonNullConstraint = false;
    Type j;
    if (a is UserDefinedType { ResolvedClass: NonNullTypeDecl aClass }) {
      joinNeedsNonNullConstraint = true;
      j = MeetX(aClass.RhsWithArgument(a.TypeArgs), b);
    } else if (b is UserDefinedType { ResolvedClass: NonNullTypeDecl bClass }) {
      joinNeedsNonNullConstraint = true;
      j = MeetX(a, bClass.RhsWithArgument(b.TypeArgs));
    } else {
      j = MeetX(a, b);
    }
    if (j != null && joinNeedsNonNullConstraint && !j.IsNonNullRefType) {
      // try to make j into a non-null type; if that's not possible, then there is no meet
      var udt = j as UserDefinedType;
      if (udt != null && udt.ResolvedClass is ClassLikeDecl { IsReferenceTypeDecl: true }) {
        // add the non-null constraint back in
        j = UserDefinedType.CreateNonNullType(udt);
      } else {
        // the original a and b have no meet
        j = null;
      }
    }
    if (systemModuleManager.Options.Get(CommonOptionBag.TypeInferenceDebug)) {
      systemModuleManager.Options.OutputWriter.WriteLine("DEBUG: Meet( {0}, {1} ) = {2}", a, b, j);
    }
    return j;
  }
  public Type MeetX(Type a, Type b) {
    Contract.Requires(a != null);
    Contract.Requires(b != null);

    a = a.NormalizeExpandKeepConstraints();
    b = b.NormalizeExpandKeepConstraints();
    if (a is IntVarietiesSupertype) {
      return b is IntVarietiesSupertype || b.IsNumericBased(Type.NumericPersuasion.Int) || b.IsBigOrdinalType || b.IsBitVectorType ? b : null;
    } else if (b is IntVarietiesSupertype) {
      return a.IsNumericBased(Type.NumericPersuasion.Int) || a.IsBigOrdinalType || a.IsBitVectorType ? a : null;
    } else if (a is RealVarietiesSupertype) {
      return b is RealVarietiesSupertype || b.IsNumericBased(Type.NumericPersuasion.Real) ? b : null;
    } else if (b is RealVarietiesSupertype) {
      return a.IsNumericBased(Type.NumericPersuasion.Real) ? a : null;
    }

    var towerA = Type.GetTowerOfSubsetTypes(a);
    var towerB = Type.GetTowerOfSubsetTypes(b);
    if (towerB.Count < towerA.Count) {
      // make A be the shorter tower
      var tmp0 = a; a = b; b = tmp0;
      var tmp1 = towerA; towerA = towerB; towerB = tmp1;
    }
    var n = towerA.Count;
    Contract.Assert(1 <= n);  // guaranteed by GetTowerOfSubsetTypes
    if (towerA.Count < towerB.Count) {
      // B is strictly taller. The meet exists only if towerA[n-1] is a supertype of towerB[n-1], and
      // then the meet is "b".
      return Type.IsSupertype(towerA[n - 1], towerB[n - 1]) ? b : null;
    }
    Contract.Assert(towerA.Count == towerB.Count);
    a = towerA[n - 1];
    b = towerB[n - 1];
    if (2 <= n) {
      var udtA = (UserDefinedType)a;
      var udtB = (UserDefinedType)b;
      if (udtA.ResolvedClass == udtB.ResolvedClass) {
        // We have two subset types with equal heads
        if (a.Equals(b, true)) {  // optimization for a special case, which applies for example when there are no arguments or when the types happen to be the same
          return a;
        }
        Contract.Assert(a.TypeArgs.Count == b.TypeArgs.Count);
        var typeArgs = Joins(TypeParameter.Variances(udtA.ResolvedClass.TypeArgs, true), a.TypeArgs, b.TypeArgs);
        if (typeArgs == null) {
          return null;
        }
        return new UserDefinedType(udtA.tok, udtA.Name, udtA.ResolvedClass, typeArgs);
      } else {
        // The two subset types do not have the same head, so there is no meet
        return null;
      }
    }
    Contract.Assert(towerA.Count == 1 && towerB.Count == 1);

    if (a.IsBoolType || a.IsCharType || a.IsNumericBased() || a.IsBitVectorType || a.IsBigOrdinalType || a.IsTypeParameter || a.IsInternalTypeSynonym || a is TypeProxy) {
      return a.Equals(b, true) ? a : null;
    } else if (a is SetType) {
      var aa = (SetType)a;
      var bb = b as SetType;
      if (bb == null || aa.Finite != bb.Finite) {
        return null;
      }
      // sets are co-variant in their argument type
      var typeArg = Meet(a.TypeArgs[0], b.TypeArgs[0]);
      return typeArg == null ? null : new SetType(aa.Finite, typeArg);
    } else if (a is MultiSetType) {
      var aa = (MultiSetType)a;
      var bb = b as MultiSetType;
      if (bb == null) {
        return null;
      }
      // multisets are co-variant in their argument type
      var typeArg = Meet(a.TypeArgs[0], b.TypeArgs[0]);
      return typeArg == null ? null : new MultiSetType(typeArg);
    } else if (a is SeqType) {
      var aa = (SeqType)a;
      var bb = b as SeqType;
      if (bb == null) {
        return null;
      }
      // sequences are co-variant in their argument type
      var typeArg = Meet(a.TypeArgs[0], b.TypeArgs[0]);
      return typeArg == null ? null : new SeqType(typeArg);
    } else if (a is MapType) {
      var aa = (MapType)a;
      var bb = b as MapType;
      if (bb == null || aa.Finite != bb.Finite) {
        return null;
      }
      // maps are co-variant in both argument types
      var typeArgDomain = Meet(a.TypeArgs[0], b.TypeArgs[0]);
      var typeArgRange = Meet(a.TypeArgs[1], b.TypeArgs[1]);
      return typeArgDomain == null || typeArgRange == null ? null : new MapType(aa.Finite, typeArgDomain, typeArgRange);
    } else if (a.IsDatatype) {
      var aa = a.AsDatatype;
      if (aa != b.AsDatatype) {
        return null;
      }
      if (a.Equals(b, true)) {  // optimization for a special case, which applies for example when there are no arguments or when the types happen to be the same
        return a;
      }
      Contract.Assert(a.TypeArgs.Count == b.TypeArgs.Count);
      var typeArgs = Joins(TypeParameter.Variances(aa.TypeArgs, true), a.TypeArgs, b.TypeArgs);
      if (typeArgs == null) {
        return null;
      }
      var udt = (UserDefinedType)a;
      return new UserDefinedType(udt.tok, udt.Name, aa, typeArgs);
    } else if (a.AsArrowType != null) {
      var aa = a.AsArrowType;
      var bb = b.AsArrowType;
      Contract.Assert(aa != null && bb != null && aa.Arity == bb.Arity);
      int arity = aa.Arity;
      Contract.Assert(a.TypeArgs.Count == arity + 1);
      Contract.Assert(b.TypeArgs.Count == arity + 1);
      Contract.Assert(aa.ResolvedClass == bb.ResolvedClass);
      var typeArgs = Joins(aa.Variances(true), a.TypeArgs, b.TypeArgs);
      return new ArrowType(aa.tok, (ArrowTypeDecl)aa.ResolvedClass, typeArgs);
    } else if (b.IsObjectQ) {
      return a.IsRefType ? a : null;
    } else if (a.IsObjectQ) {
      return b.IsRefType ? b : null;
    } else {
      // "a" is a class, trait, or abstract type
      var aa = ((UserDefinedType)a).ResolvedClass;
      Contract.Assert(aa != null);
      if (!(b is UserDefinedType)) {
        return null;
      }
      var bb = ((UserDefinedType)b).ResolvedClass;
      if (a.Equals(b, true)) {  // optimization for a special case, which applies for example when there are no arguments or when the types happen to be the same
        return a;
      } else if (aa == bb) {
        Contract.Assert(a.TypeArgs.Count == b.TypeArgs.Count);
        var typeArgs = Joins(TypeParameter.Variances(aa.TypeArgs, true), a.TypeArgs, b.TypeArgs);
        if (typeArgs == null) {
          return null;
        }
        var udt = (UserDefinedType)a;
        return new UserDefinedType(udt.tok, udt.Name, aa, typeArgs);
      } else if (aa is ClassLikeDecl && bb is ClassLikeDecl) {
        if (a.IsSubtypeOf(b, false, false)) {
          return a;
        } else if (b.IsSubtypeOf(a, false, false)) {
          return b;
        } else {
          return null;
        }
      } else {
        return null;
      }
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
