//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.IO;
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
        flows.Add(new FlowFromComputedType(expr, seqType, sourceType => new SeqType(sourceType.NormalizeExpand().TypeArgs[0])));
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
    }
    else if (expr is ITEExpr iteExpr) {
      var proxy = PreType2UpdatableType(expr.PreType);
      expr.UnnormalizedType = proxy;
      AddConstraint(proxy, iteExpr.Thn, "if-then", iteExpr.tok);
      AddConstraint(proxy, iteExpr.Els, "if-else", iteExpr.tok);
    } else if (expr is ConcreteSyntaxExpression { ResolvedExpression: { } resolvedExpression }) {
      expr.UnnormalizedType = resolvedExpression.UnnormalizedType;
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

  record FlowContext(SystemModuleManager SystemModuleManager, ErrorReporter Reporter, bool DebugPrint) {
    public TextWriter OutputWriter => SystemModuleManager.Options.OutputWriter;
  }

  abstract class Flow {
    private readonly IToken tok;
    private readonly string description;

    protected string TokDescription() {
      return $"({tok.line},{tok.col}) {description}";
    }

    /// <summary>
    /// Start flow from source to sink and return whether or not anything changed.
    /// </summary>
    public abstract bool Update(FlowContext context);

    protected Flow(IToken tok, string description) {
      this.tok = tok;
      this.description = description;
    }

    public abstract void DebugPrint(TextWriter output);

    protected static bool EqualTypes(Type a, Type b) {
      if (a is BottomTypePlaceholder != b is BottomTypePlaceholder) {
        return false;
      }
      return a.Equals(b, true);
    }

    /// <summary>
    /// Does a best-effort to compute the join of "a" and "b", where the base types of "a" and "b" (or
    /// some parent type thereof) are the same.
    /// If there is no join (for example, if type parameters in a non-variant position are
    /// incompatible), then use base types as such type arguments.
    /// </summary>
    public static Type Join(Type a, Type b, FlowContext context) {
      Contract.Requires(a != null);
      Contract.Requires(b != null);

      if (a is BottomTypePlaceholder) {
        return b;
      } else if (b is BottomTypePlaceholder) {
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
          var typeArgs = Joins(TypeParameter.Variances(udtA.ResolvedClass.TypeArgs), a.TypeArgs, b.TypeArgs, context);
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
        var typeArgs = Joins(directions, a.TypeArgs, b.TypeArgs, context);
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
        var typeArgs = Joins(aa.Variances(), a.TypeArgs, b.TypeArgs, context);
        return new ArrowType(aa.tok, (ArrowTypeDecl)aa.ResolvedClass, typeArgs);
      }

      // Convert a and b to their common supertype
      var aDecl = (TopLevelDeclWithMembers)((UserDefinedType)a).ResolvedClass;
      var bDecl = (TopLevelDeclWithMembers)((UserDefinedType)b).ResolvedClass;
      var commonSupertypeDecl = PreTypeConstraints.JoinHeads(aDecl, bDecl, context.SystemModuleManager);
      Contract.Assert(commonSupertypeDecl != null);
      var aTypeSubstMap = TypeParameter.SubstitutionMap(aDecl.TypeArgs, a.TypeArgs);
      aDecl.AddParentTypeParameterSubstitutions(aTypeSubstMap);
      var bTypeSubstMap = TypeParameter.SubstitutionMap(bDecl.TypeArgs, b.TypeArgs);
      bDecl.AddParentTypeParameterSubstitutions(bTypeSubstMap);

      a = UserDefinedType.FromTopLevelDecl(commonSupertypeDecl.tok, commonSupertypeDecl).Subst(aTypeSubstMap);
      b = UserDefinedType.FromTopLevelDecl(commonSupertypeDecl.tok, commonSupertypeDecl).Subst(bTypeSubstMap);

      var joinedTypeArgs = Joins(TypeParameter.Variances(commonSupertypeDecl.TypeArgs), a.TypeArgs, b.TypeArgs, context);
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
    public static Type Meet(Type a, Type b, FlowContext context) {
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
    public static List<Type> Joins(List<TypeParameter.TPVariance> directions, List<Type> a, List<Type> b, FlowContext context) {
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
          output = Join(a[i], b[i], context);
        } else if (directions[i] == TypeParameter.TPVariance.Contra) {
          output = Meet(a[i], b[i], context);
        } else {
          Contract.Assert(directions[i] == TypeParameter.TPVariance.Non);
          if (AdjustableType.NormalizesToBottom(a[i])) {
            output = b[i];
          } else if (AdjustableType.NormalizesToBottom(b[i])) {
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

  class FlowFromType : Flow {
    private readonly Type sink;
    private readonly Type source;

    public FlowFromType(Type sink, Type source, IToken tok, string description = "")
      : base(tok, description) {
      this.sink = AdjustableType.NormalizeSansAdjustableType(sink);
      this.source = source;
    }

    public FlowFromType(Expression sink, Type source)
      : base(sink.tok, "") {
      this.sink = sink.UnnormalizedType;
      this.source = source;
    }

    protected virtual Type GetSourceType() {
      return source;
    }

    public override bool Update(FlowContext context) {
      var sourceType = GetSourceType();
      if (sink is AdjustableType adjustableType && !EqualTypes(adjustableType.T, sourceType)) {
        adjustableType.T = sourceType;
        return true;
      }
      // TODO: perhaps it's still possible to update the type arguments
      return false;
    }

    public override void DebugPrint(TextWriter output) {
      if (sink is AdjustableType adjustableType) {
        var bound = PreTypeConstraints.Pad($"%{adjustableType.UniqueId} :> {AdjustableType.ToStringAsAdjustableType(source)}", 27);
        var value = PreTypeConstraints.Pad(AdjustableType.ToStringAsBottom(adjustableType), 20);
        output.WriteLine($"    {bound}  {value}    {TokDescription()}");
      }
    }
  }

  class FlowFromTypeArgument : FlowFromType {
    private readonly int argumentIndex;

    public FlowFromTypeArgument(Expression sink, Type source, int argumentIndex)
      : base(sink, source) {
      Contract.Requires(0 <= argumentIndex);
      this.argumentIndex = argumentIndex;
    }

    protected override Type GetSourceType() {
      var sourceType = base.GetSourceType().NormalizeExpand();
      Contract.Assert(argumentIndex < sourceType.TypeArgs.Count);
      return sourceType.TypeArgs[argumentIndex];
    }
  }

  class FlowFromComputedType : FlowFromType {
    private readonly System.Func<Type, Type> getType;

    public FlowFromComputedType(Expression sink, Type source, System.Func<Type, Type> getType)
      : base(sink, source) {
      this.getType = getType;
    }

    protected override Type GetSourceType() {
      var sourceType = base.GetSourceType().NormalizeExpand();
      return getType(sourceType);
    }
  }

  class FlowIntoVariable : Flow {
    protected readonly AdjustableType sink;
    protected readonly Expression source;

    protected Type Lhs {
      get => sink.T;
      set => sink.T = value;
    }

    public FlowIntoVariable(IVariable variable, Expression source, IToken tok, string description = ":=")
      : base(tok, description) {
      Contract.Requires(AdjustableType.NormalizeSansAdjustableType(variable.UnnormalizedType) is AdjustableType);
      this.sink = (AdjustableType)AdjustableType.NormalizeSansAdjustableType(variable.UnnormalizedType);
      this.source = source;
    }

    public override bool Update(FlowContext context) {
      var previousLhs = Lhs;
      var join = Join(Lhs, source.Type, context);
      if (!EqualTypes(Lhs, join)) {
        if (context.DebugPrint) {
          context.OutputWriter.WriteLine(
            $"DEBUG: updating proxy %{sink.UniqueId} to {AdjustableType.ToStringAsAdjustableType(Lhs)}" +
            $" ({AdjustableType.ToStringAsBottom(previousLhs)} \\/ {AdjustableType.ToStringAsBottom(source.Type)})");
        }
        Lhs = join;
        return true;
      }
      return false;
    }

    public override void DebugPrint(TextWriter output) {
      var bound = PreTypeConstraints.Pad($"%{sink.UniqueId} :> {AdjustableType.ToStringAsAdjustableType(source.UnnormalizedType)}", 27);
      var value = PreTypeConstraints.Pad(AdjustableType.ToStringAsBottom(sink), 20);
      output.WriteLine($"    {bound}  {value}    {TokDescription()}");
    }
  }
}
