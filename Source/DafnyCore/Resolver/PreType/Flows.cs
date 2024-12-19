//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.IO;
using JetBrains.Annotations;

namespace Microsoft.Dafny;

record FlowContext(SystemModuleManager SystemModuleManager, ErrorReporter Reporter, bool DebugPrint) {
  public TextWriter OutputWriter => SystemModuleManager.Options.OutputWriter;
}

/// <summary>
/// A "Flow" is a puzzle piece in recomputing types. The "type refinement" phase defines a set of flows and then
/// recomputes types until it reaches a fix point.
///
/// For example, the type refinement phase will use a FlowIntoVariable to define a flow from the RHS of an assignment to
/// the LHS. It will use a FlowBetweenExpressions to define a flow from the "then" branch of an "if-then-else" expression
/// to the "if-then-else" expression itself, and will use another FlowBetweenExpressions to define the analogous flow from
/// the "else" branch.
///
/// For more information about type refinements, flow, and the whole type inference process, see docs/dev/TypeSystemRefresh.md.
/// </summary>
abstract class Flow {
  private readonly IOrigin tok;
  private readonly string description;
  public bool HasError;

  protected string TokDescription() {
    return $"({tok.line},{tok.col}) {description}";
  }

  /// <summary>
  /// Start flow from source to sink and return whether or not anything changed.
  /// </summary>
  public abstract bool Update(FlowContext context);

  protected Flow(IOrigin tok, string description) {
    this.tok = tok;
    this.description = description;
  }

  public abstract void DebugPrint(TextWriter output);

  protected bool UpdateTypeHeldByRefinementWrapper(Type sink, Type sourceType, FlowContext context) {
    string previousLhs = null;
    string joinArguments = null;
    if (context.DebugPrint) {
      previousLhs = $"{TypeRefinementWrapper.ToStringShowingWrapper(sink)}";
      joinArguments = $"{TypeRefinementWrapper.ToStringAsBottom(sink)} \\/ {TypeRefinementWrapper.ToStringAsBottom(sourceType)}";
    }

    var previousSink = (TypeRefinementWrapper.NormalizeSansRefinementWrappers(sink) as TypeRefinementWrapper)?.T ?? sink;
    var join = JoinAndUpdate(sink, sourceType, context);
    if (join == null) {
      HasError = true;
      return false;
    }
    if (EqualTypes(previousSink, sink)) {
      return false;
    }
    if (context.DebugPrint) {
      context.OutputWriter.WriteLine($"DEBUG: refining {previousLhs} to {TypeRefinementWrapper.ToStringAsBottom(sink)} ({joinArguments})");
    }
    return true;
  }

  protected static bool EqualTypes(Type a, Type b) {
    if (TypeRefinementWrapper.NormalizesToBottom(a) != TypeRefinementWrapper.NormalizesToBottom(b)) {
      return false;
    }
    return a.Equals(b, true);
  }

  [CanBeNull]
  public static Type JoinAndUpdate(Type a, Type b, FlowContext context) {
    var wrapperA = TypeRefinementWrapper.NormalizeSansRefinementWrappers(a) as TypeRefinementWrapper;
    var wrapperB = TypeRefinementWrapper.NormalizeSansRefinementWrappers(b) as TypeRefinementWrapper;
    var join = Join(wrapperA?.T ?? a, wrapperB?.T ?? b, context);
    if (join == null) {
      return null;
    }
    if (wrapperA == null) {
      return join;
    }

    if (TypeRefinementWrapper.NormalizeSansRefinementWrappers(join) is TypeRefinementWrapper wrapperJoin) {
      join = wrapperJoin.T;
    }
    wrapperA.T = join;
    return wrapperA;
  }

  [CanBeNull]
  public static Type CopyAndUpdate(Type a, Type b, FlowContext context) {
    var wrapperA = TypeRefinementWrapper.NormalizeSansRefinementWrappers(a) as TypeRefinementWrapper;
    // compute the "copy" of aa and b:
    Type copy;
    if (TypeRefinementWrapper.NormalizesToBottom(a)) {
      copy = b;
    } else if (TypeRefinementWrapper.NormalizesToBottom(b)) {
      copy = a;
    } else if (a.Equals(b, true)) {
      copy = a;
    } else {
      return null;
    }

    if (wrapperA == null) {
      return copy;
    }

    copy = TypeRefinementWrapper.NormalizeSansRefinementWrappers(copy);
    if (copy is TypeRefinementWrapper wrapperCopy) {
      copy = wrapperCopy.T;
    }
    wrapperA.T = copy;
    return wrapperA;
  }

  /// <summary>
  /// Does a best-effort to compute the join of "a" and "b", where the base types of "a" and "b" (or
  /// some parent type thereof) are the same.
  /// If there is no join (for example, if type parameters in a non-variant position are
  /// incompatible), then return null;
  /// </summary>
  [CanBeNull]
  public static Type Join(Type a, Type b, FlowContext context) {
    Contract.Requires(a != null);
    Contract.Requires(b != null);

    [CanBeNull]
    Type JoinChildren(UserDefinedType udtA, UserDefinedType udtB) {
      if (udtA.ResolvedClass == udtB.ResolvedClass) {
        // We have two subset types with equal heads
        Contract.Assert(a.TypeArgs.Count == b.TypeArgs.Count);
        var typeArgs = Joins(TypeParameter.Variances(udtA.ResolvedClass.TypeArgs), a.TypeArgs, b.TypeArgs, context);
        if (typeArgs != null) {
          return UserDefinedType.FromTopLevelDecl(udtA.Tok, udtA.ResolvedClass, typeArgs);
        }
      }
      return null;
    }

    if (a is BottomTypePlaceholder) {
      return b;
    } else if (b is BottomTypePlaceholder) {
      return a;
    }

    // Before we do anything else, make a note of whether or not both "a" and "b" are non-null types.
    var abNonNullTypes = a.IsNonNullRefType && b.IsNonNullRefType;

    var towerA = Type.GetTowerOfSubsetTypes(a, true);
    var towerB = Type.GetTowerOfSubsetTypes(b, true);
    // We almost expect the base types of these towers to be the same, since the module has successfully gone through pre-resolution and the
    // pre-resolution underspecification checks. However, there are considerations.
    //   - One is that the two given types may contain unused type parameters in type synonyms or subset types, and pre-resolution does not
    //     fill those in or detect their absence.
    //   - The other is traits.
    for (var n = System.Math.Min(towerA.Count, towerB.Count); 1 <= --n;) {
      a = towerA[n];
      b = towerB[n];
      var join = JoinChildren((UserDefinedType)a, (UserDefinedType)b);
      if (join != null) {
        return join;
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
      if (typeArgs == null) {
        return null;
      }
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
      if (typeArgs == null) {
        return null;
      }
      return new ArrowType(aa.Tok, (ArrowTypeDecl)aa.ResolvedClass, typeArgs);
    }

    // Convert a and b to their common supertype
    var aDecl = ((UserDefinedType)a).ResolvedClass;
    var bDecl = ((UserDefinedType)b).ResolvedClass;
    var commonSupertypeDecl = PreTypeConstraints.JoinHeads(aDecl, bDecl, context.SystemModuleManager);
    Contract.Assert(commonSupertypeDecl != null);
    var aTypeSubstMap = TypeParameter.SubstitutionMap(aDecl.TypeArgs, a.TypeArgs);
    (aDecl as TopLevelDeclWithMembers)?.AddParentTypeParameterSubstitutions(aTypeSubstMap);
    var bTypeSubstMap = TypeParameter.SubstitutionMap(bDecl.TypeArgs, b.TypeArgs);
    (bDecl as TopLevelDeclWithMembers)?.AddParentTypeParameterSubstitutions(bTypeSubstMap);

    var aSubst = UserDefinedType.FromTopLevelDecl(commonSupertypeDecl.Tok, commonSupertypeDecl).Subst(aTypeSubstMap);
    var bSubst = UserDefinedType.FromTopLevelDecl(commonSupertypeDecl.Tok, commonSupertypeDecl).Subst(bTypeSubstMap);

    var joinedTypeArgs = Joins(TypeParameter.Variances(commonSupertypeDecl.TypeArgs), aSubst.TypeArgs, bSubst.TypeArgs, context);
    if (joinedTypeArgs == null) {
      return null;
    }
    var result = UserDefinedType.FromTopLevelDecl(a.Tok, commonSupertypeDecl, joinedTypeArgs);
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
  [CanBeNull]
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
        output = JoinAndUpdate(a[i], b[i], context);
      } else if (directions[i] == TypeParameter.TPVariance.Contra) {
        output = Meet(a[i], b[i], context);
      } else {
        Contract.Assert(directions[i] == TypeParameter.TPVariance.Non);
        output = CopyAndUpdate(a[i], b[i], context);
      }
      if (output == null) {
        return null;
      }
      extrema.Add(output);
    }
    return extrema;
  }
}


class FlowIntoVariable : Flow {
  protected readonly Type sink;
  protected readonly Expression source;

  public FlowIntoVariable(IVariable variable, Expression source, IOrigin tok, string description = ":=")
    : base(tok, description) {
    this.sink = TypeRefinementWrapper.NormalizeSansRefinementWrappers(variable.UnnormalizedType);
    this.source = source;
  }

  public override bool Update(FlowContext context) {
    return UpdateTypeHeldByRefinementWrapper(sink, TypeRefinementWrapper.NormalizeSansBottom(source), context);
  }

  public override void DebugPrint(TextWriter output) {
    var lhs = TypeRefinementWrapper.ToStringShowingWrapper(sink);
    var rhs = TypeRefinementWrapper.ToStringShowingWrapper(source.UnnormalizedType);
    var bound = PreTypeConstraints.Pad($"{lhs} :> {rhs}", 27);
    var value = PreTypeConstraints.Pad(TypeRefinementWrapper.ToStringAsBottom(sink), 20);
    output.WriteLine($"    {bound}  {value}    {TokDescription()}");
  }
}

class FlowIntoVariableFromComputedType : Flow {
  protected readonly Type sink;
  private readonly System.Func<Type> getType;

  public FlowIntoVariableFromComputedType(IVariable variable, System.Func<Type> getType, IOrigin tok, string description = ":=")
    : base(tok, description) {
    this.sink = TypeRefinementWrapper.NormalizeSansRefinementWrappers(variable.UnnormalizedType);
    this.getType = getType;
  }

  public override bool Update(FlowContext context) {
    return UpdateTypeHeldByRefinementWrapper(sink, getType(), context);
  }

  public override void DebugPrint(TextWriter output) {
    var sourceType = getType();
    var bound = PreTypeConstraints.Pad($"{TypeRefinementWrapper.ToStringShowingWrapper(sink)} :> {TypeRefinementWrapper.ToStringShowingWrapper(sourceType)}", 27);
    var value = PreTypeConstraints.Pad(TypeRefinementWrapper.ToStringAsBottom(sink), 20);
    output.WriteLine($"    {bound}  {value}    {TokDescription()}");
  }
}

class FlowBetweenComputedTypes : Flow {
  private readonly System.Func<(Type, Type)> getTypes;

  public FlowBetweenComputedTypes(System.Func<(Type, Type)> getTypes, IOrigin tok, string description)
    : base(tok, description) {
    this.getTypes = getTypes;
  }

  public override bool Update(FlowContext context) {
    var (sink, source) = getTypes();
    return UpdateTypeHeldByRefinementWrapper(sink, source, context);
  }

  public override void DebugPrint(TextWriter output) {
    var (sink, source) = getTypes();
    var bound = PreTypeConstraints.Pad($"{TypeRefinementWrapper.ToStringShowingWrapper(sink)} :> {TypeRefinementWrapper.ToStringShowingWrapper(source)}", 27);
    var value = PreTypeConstraints.Pad(TypeRefinementWrapper.ToStringAsBottom(sink), 20);
    output.WriteLine($"    {bound}  {value}    {TokDescription()}");
  }
}

abstract class FlowIntoExpr : Flow {
  private readonly Type sink;

  protected FlowIntoExpr(Type sink, IOrigin tok, string description = "")
    : base(tok, description) {
    this.sink = TypeRefinementWrapper.NormalizeSansRefinementWrappers(sink);
  }

  protected FlowIntoExpr(Expression sink, IOrigin tok, string description = "")
    : base(sink.Tok, description) {
    this.sink = sink.UnnormalizedType;
  }

  protected abstract Type GetSourceType();

  public override bool Update(FlowContext context) {
    return UpdateTypeHeldByRefinementWrapper(sink, GetSourceType(), context);
  }

  public override void DebugPrint(TextWriter output) {
    var sourceType = GetSourceType();
    var bound = PreTypeConstraints.Pad($"{TypeRefinementWrapper.ToStringShowingWrapper(sink)} :> {TypeRefinementWrapper.ToStringShowingWrapper(sourceType)}", 27);
    var value = PreTypeConstraints.Pad(TypeRefinementWrapper.ToStringAsBottom(sink), 20);
    output.WriteLine($"    {bound}  {value}    {TokDescription()}");
  }
}

class FlowFromType : FlowIntoExpr {
  private readonly Type source;

  public FlowFromType(Type sink, Type source, IOrigin tok, string description = "")
    : base(sink, tok, description) {
    this.source = source;
  }

  public FlowFromType(Expression sink, Type source, string description = "")
    : base(sink, sink.Tok, description) {
    this.source = source;
  }

  protected override Type GetSourceType() {
    return source;
  }
}

class FlowFromTypeArgument : FlowIntoExpr {
  private readonly Type source;
  private readonly int argumentIndex;

  public FlowFromTypeArgument(Expression sink, Type source, int argumentIndex)
    : base(sink, sink.Tok) {
    Contract.Requires(0 <= argumentIndex);
    this.source = source;
    this.argumentIndex = argumentIndex;
  }

  protected override Type GetSourceType() {
    var sourceType = source.NormalizeToAncestorType();
    Contract.Assert(argumentIndex < sourceType.TypeArgs.Count);
    return sourceType.TypeArgs[argumentIndex];
  }
}

class FlowFromTypeArgumentOfComputedSource : FlowIntoExpr {
  private readonly System.Func<Type> getType;
  private readonly int argumentIndex;

  public FlowFromTypeArgumentOfComputedSource(Expression sink, System.Func<Type> getType, int argumentIndex)
    : base(sink, sink.Tok) {
    Contract.Requires(0 <= argumentIndex);
    this.getType = getType;
    this.argumentIndex = argumentIndex;
  }

  protected override Type GetSourceType() {
    var sourceType = getType().NormalizeExpand();
    Contract.Assert(argumentIndex < sourceType.TypeArgs.Count);
    return sourceType.TypeArgs[argumentIndex];
  }
}

class FlowFromComputedType : FlowIntoExpr {
  private readonly System.Func<Type> getType;

  public FlowFromComputedType(Expression sink, System.Func<Type> getType, string description = "")
    : base(sink, sink.Tok, description) {
    this.getType = getType;
  }

  protected override Type GetSourceType() {
    return getType();
  }
}

class FlowFromComputedTypeIgnoreHeadTypes : FlowIntoExpr {
  private readonly System.Func<Type> getType;

  public FlowFromComputedTypeIgnoreHeadTypes(Expression sink, System.Func<Type> getType, string description = "")
    : base(sink.Type.NormalizeToAncestorType(), sink.Tok, description) {
    this.getType = getType;
  }

  protected override Type GetSourceType() {
    return getType();
  }
}

class FlowBetweenExpressions : FlowIntoExpr {
  private readonly Expression source;

  public FlowBetweenExpressions(Expression sink, Expression source, string description = "")
    : base(sink, sink.Tok, description) {
    this.source = source;
  }

  protected override Type GetSourceType() {
    return TypeRefinementWrapper.NormalizeSansBottom(source);
  }
}
