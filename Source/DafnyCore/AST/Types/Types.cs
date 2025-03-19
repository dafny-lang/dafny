#define TI_DEBUG_PRINT
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

/// <summary>
/// An ArtificialType is only used during type checking. It should never be assigned as the type of any expression.
/// It works as a supertype to numeric literals. For example, the literal 6 can be an "int", a "bv16", a
/// newtype based on integers, or an "ORDINAL". Type inference thus uses an "artificial" supertype of all of
/// these types as the type of literal 6, until a more precise (and non-artificial) type is inferred for it.
/// </summary>
public abstract class ArtificialType : Type {
  public override bool ComputeMayInvolveReferences(ISet<DatatypeDecl>/*?*/ visitedDatatypes) {
    // ArtificialType's are used only with numeric types.
    return false;
  }

  public override Type Subst(IDictionary<TypeParameter, Type> subst) {
    throw new NotSupportedException();
  }

  public override Type ReplaceTypeArguments(List<Type> arguments) {
    throw new NotSupportedException();
  }
}
/// <summary>
/// The type "IntVarietiesSupertype" is used to denote a decimal-less number type, namely an int-based type
/// or a bitvector type.
/// </summary>
public class IntVarietiesSupertype : ArtificialType {
  [System.Diagnostics.Contracts.Pure]
  public override string TypeName(DafnyOptions options, ModuleDefinition context, bool parseAble) {
    return "int";
  }
  public override bool Equals(Type that, bool keepConstraints = false) {
    return keepConstraints ? this.GetType() == that.GetType() : that is IntVarietiesSupertype;
  }
}
public class RealVarietiesSupertype : ArtificialType {
  [System.Diagnostics.Contracts.Pure]
  public override string TypeName(DafnyOptions options, ModuleDefinition context, bool parseAble) {
    return "real";
  }
  public override bool Equals(Type that, bool keepConstraints = false) {
    return keepConstraints ? this.GetType() == that.GetType() : that is RealVarietiesSupertype;
  }
}

/// <summary>
/// A NonProxy type is a fully constrained type.  It may contain members.
/// </summary>
public abstract class NonProxyType : Type {
  [SyntaxConstructor]
  protected NonProxyType(IOrigin origin = null) : base(origin) {
  }

  protected NonProxyType(Cloner cloner, NonProxyType original) : base(cloner, original) {
  }
}

public abstract class BasicType : NonProxyType {

  protected BasicType() : base(null) {
  }

  [SyntaxConstructor]
  protected BasicType(IOrigin origin) : base(origin) {
  }

  protected BasicType(Cloner cloner, NonProxyType original) : base(cloner, original) {
  }

  public override IEnumerable<INode> Children => Enumerable.Empty<Node>();
  public override bool ComputeMayInvolveReferences(ISet<DatatypeDecl>/*?*/ visitedDatatypes) {
    return false;
  }

  public override Type Subst(IDictionary<TypeParameter, Type> subst) {
    return this;
  }

  public override Type ReplaceTypeArguments(List<Type> arguments) {
    return this;
  }
}

public class BoolType : BasicType {
  [SyntaxConstructor]
  public BoolType(IOrigin origin) : base(origin) { }

  public BoolType() { }

  [Pure]
  public override string TypeName(DafnyOptions options, ModuleDefinition context, bool parseAble) {
    return "bool";
  }
  public override bool Equals(Type that, bool keepConstraints = false) {
    return that.IsBoolType;
  }
}

public class CharType : BasicType {
  public const char DefaultValue = 'D';
  public const string DefaultValueAsString = "'D'";
  [System.Diagnostics.Contracts.Pure]
  public override string TypeName(DafnyOptions options, ModuleDefinition context, bool parseAble) {
    return "char";
  }
  public override bool Equals(Type that, bool keepConstraints = false) {
    return that.IsCharType;
  }
}

public class IntType : BasicType {

  [SyntaxConstructor]
  public IntType(IOrigin origin) : base(origin) {
  }

  public IntType() {
  }

  [Pure]
  public override string TypeName(DafnyOptions options, ModuleDefinition context, bool parseAble) {
    return "int";
  }
  public override bool Equals(Type that, bool keepConstraints = false) {
    return that.NormalizeExpand(keepConstraints) is IntType;
  }
  public override bool IsSubtypeOf(Type super, bool ignoreTypeArguments, bool ignoreNullity) {
    if (super is IntVarietiesSupertype) {
      return true;
    }
    return base.IsSubtypeOf(super, ignoreTypeArguments, ignoreNullity);
  }
}

public class RealType : BasicType {
  [System.Diagnostics.Contracts.Pure]
  public override string TypeName(DafnyOptions options, ModuleDefinition context, bool parseAble) {
    return "real";
  }
  public override bool Equals(Type that, bool keepConstraints = false) {
    return that.NormalizeExpand(keepConstraints) is RealType;
  }
  public override bool IsSubtypeOf(Type super, bool ignoreTypeArguments, bool ignoreNullity) {
    if (super is RealVarietiesSupertype) {
      return true;
    }
    return base.IsSubtypeOf(super, ignoreTypeArguments, ignoreNullity);
  }
}

public class BigOrdinalType : BasicType {
  [System.Diagnostics.Contracts.Pure]
  public override string TypeName(DafnyOptions options, ModuleDefinition context, bool parseAble) {
    return "ORDINAL";
  }
  public override bool Equals(Type that, bool keepConstraints = false) {
    return that.NormalizeExpand(keepConstraints) is BigOrdinalType;
  }
  public override bool IsSubtypeOf(Type super, bool ignoreTypeArguments, bool ignoreNullity) {
    if (super is IntVarietiesSupertype) {
      return true;
    }
    return base.IsSubtypeOf(super, ignoreTypeArguments, ignoreNullity);
  }
}

public class BitvectorType : BasicType {
  public readonly int Width;
  public readonly NativeType NativeType;
  public BitvectorType(DafnyOptions options, int width)
    : base() {
    Contract.Requires(0 <= width);
    Width = width;
    foreach (var nativeType in ModuleResolver.NativeTypes) {
      if (options.Backend.SupportedNativeTypes.Contains(nativeType.Name) && width <= nativeType.Bitwidth) {
        NativeType = nativeType;
        break;
      }
    }
  }

  public string Name => "bv" + Width;

  [System.Diagnostics.Contracts.Pure]
  public override string TypeName(DafnyOptions options, ModuleDefinition context, bool parseAble) {
    return Name;
  }
  public override bool Equals(Type that, bool keepConstraints = false) {
    var bv = that.NormalizeExpand(keepConstraints) as BitvectorType;
    return bv != null && bv.Width == Width;
  }
  public override bool IsSubtypeOf(Type super, bool ignoreTypeArguments, bool ignoreNullity) {
    if (super is IntVarietiesSupertype) {
      return true;
    }
    return base.IsSubtypeOf(super, ignoreTypeArguments, ignoreNullity);
  }
}

public class SelfType : NonProxyType {
  public TypeParameter TypeArg;
  public Type ResolvedType;
  public SelfType() : base() {
    TypeArg = new TypeParameter(SourceOrigin.NoToken, new Name("selfType"), TPVarianceSyntax.NonVariant_Strict);
  }

  [System.Diagnostics.Contracts.Pure]
  public override string TypeName(DafnyOptions options, ModuleDefinition context, bool parseAble) {
    return "selftype";
  }
  public override bool Equals(Type that, bool keepConstraints = false) {
    return that.NormalizeExpand(keepConstraints) is SelfType;
  }

  public override Type Subst(IDictionary<TypeParameter, Type> subst) {
    if (subst.TryGetValue(TypeArg, out var t)) {
      return t;
    } else {
      // SelfType's are used only in certain restricted situations. In those situations, we need to be able
      // to substitute for the the SelfType's TypeArg. That's the only case in which we expect to see a
      // SelfType being part of a substitution operation at all.
      Contract.Assert(false); throw new cce.UnreachableException();
    }
  }

  public override Type ReplaceTypeArguments(List<Type> arguments) {
    throw new NotSupportedException();
  }

  public override bool ComputeMayInvolveReferences(ISet<DatatypeDecl>/*?*/ visitedDatatypes) {
    // SelfType is used only with bitvector types
    return false;
  }
}

public abstract class CollectionType : NonProxyType {
  public abstract string CollectionTypeName { get; }
  public override IEnumerable<Node> Nodes => TypeArgs.SelectMany(ta => ta.Nodes);

  public override string TypeName(DafnyOptions options, ModuleDefinition context, bool parseAble) {
    Contract.Ensures(Contract.Result<string>() != null);
    var targs = HasTypeArg() ? this.TypeArgsToString(options, context, parseAble) : "";
    return CollectionTypeName + targs;
  }
  public Type Arg {
    get {
      Contract.Ensures(Contract.Result<Type>() != null);  // this is true only after "arg" has really been set (i.e., it follows from the precondition)
      Contract.Assume(arg != null);  // This is really a precondition.  Don't call Arg until "arg" has been set.
      return arg;
    }
  }  // denotes the Domain type for a Map

  [FilledInDuringResolution]
  private Type arg;
  public Type ValueArg => TypeArgs.Last();

  // The following methods, HasTypeArg and SetTypeArg/SetTypeArgs, are to be called during resolution to make sure that "arg" becomes set.
  public bool HasTypeArg() {
    return arg != null;
  }
  public void SetTypeArg(Type arg) {
    Contract.Requires(arg != null);
    Contract.Assume(this.arg == null);  // Can only set it once.  This is really a precondition.
    this.arg = arg;

    Debug.Assert(TypeArgs.Count == 0);
    TypeArgs.Add(arg);
  }
  public virtual void SetTypeArgs(Type arg, Type other) {
    Contract.Requires(arg != null);
    Contract.Requires(other != null);
    Contract.Assume(this.arg == null);  // Can only set it once.  This is really a precondition.
    this.arg = arg;

    Debug.Assert(TypeArgs.Count == 0);
    TypeArgs.Add(arg);
    TypeArgs.Add(other);
  }
  [ContractInvariantMethod]
  void ObjectInvariant() {
    // Contract.Invariant(Contract.ForAll(TypeArgs, tp => tp != null));
    // After resolution, the following is invariant:  Contract.Invariant(Arg != null);
    // However, it may not be true until then.
  }
  /// <summary>
  /// This constructor is a collection types with 1 type argument
  /// </summary>
  protected CollectionType(Type arg) {
    this.arg = arg;
    TypeArgs = new List<Type>(1);
    if (arg != null) {
      TypeArgs.Add(arg);
    }
  }

  /// <summary>
  /// This constructor is a collection types with 2 type arguments
  /// </summary>
  protected CollectionType(Type arg, Type other) {
    this.arg = arg;
    TypeArgs = new List<Type>(2);
    if (arg != null && other != null) {
      TypeArgs.Add(arg);
      TypeArgs.Add(other);
    }
    Debug.Assert(arg == null && other == null || arg != null && other != null);
  }

  protected CollectionType(Cloner cloner, CollectionType original) {
    this.arg = cloner.CloneType(original.arg);
  }

  public override bool ComputeMayInvolveReferences(ISet<DatatypeDecl> visitedDatatypes) {
    return Arg.ComputeMayInvolveReferences(visitedDatatypes);
  }

  /// <summary>
  /// This property returns the ResolvedOpcode for the "in" operator when used with this collection type.
  /// </summary>
  public abstract BinaryExpr.ResolvedOpcode ResolvedOpcodeForIn { get; }

  /// <summary>
  /// For a given "source", denoting an expression of this CollectionType, return the BoundedPool corresponding
  /// to an expression "x in source".
  /// </summary>
  public abstract CollectionBoundedPool GetBoundedPool(Expression source);
}

public class SetType : CollectionType {
  private bool finite;

  public bool Finite {
    get { return finite; }
    set { finite = value; }
  }

  public SetType(bool finite, Type arg) : base(arg) {
    this.finite = finite;
  }
  public override string CollectionTypeName { get { return finite ? "set" : "iset"; } }
  [System.Diagnostics.Contracts.Pure]
  public override bool Equals(Type that, bool keepConstraints = false) {
    var t = that.NormalizeExpand(keepConstraints) as SetType;
    return t != null && Finite == t.Finite && Arg.Equals(t.Arg, keepConstraints);
  }

  public override Type Subst(IDictionary<TypeParameter, Type> subst) {
    var arg = Arg.Subst(subst);
    if (arg is InferredTypeProxy) {
      ((InferredTypeProxy)arg).KeepConstraints = true;
    }
    return arg == Arg ? this : new SetType(Finite, arg);
  }

  public override Type ReplaceTypeArguments(List<Type> arguments) {
    return new SetType(Finite, arguments[0]);
  }

  public override bool SupportsEquality {
    get {
      // Sets always support equality, because there is a check that the set element type always does.
      return true;
    }
  }

  public override BinaryExpr.ResolvedOpcode ResolvedOpcodeForIn => BinaryExpr.ResolvedOpcode.InSet;
  public override CollectionBoundedPool GetBoundedPool(Expression source) {
    return new SetBoundedPool(source, Arg, Arg, Finite);
  }
}

public class MultiSetType : CollectionType {
  public MultiSetType(Type arg) : base(arg) {
  }
  public override string CollectionTypeName { get { return "multiset"; } }
  public override bool Equals(Type that, bool keepConstraints = false) {
    var t = that.NormalizeExpand(keepConstraints) as MultiSetType;
    return t != null && Arg.Equals(t.Arg, keepConstraints);
  }

  public override Type Subst(IDictionary<TypeParameter, Type> subst) {
    var arg = Arg.Subst(subst);
    if (arg is InferredTypeProxy) {
      ((InferredTypeProxy)arg).KeepConstraints = true;
    }
    return arg == Arg ? this : new MultiSetType(arg);
  }

  public override Type ReplaceTypeArguments(List<Type> arguments) {
    return new MultiSetType(arguments[0]);
  }

  public override bool SupportsEquality {
    get {
      // Multisets always support equality, because there is a check that the set element type always does.
      return true;
    }
  }

  public override BinaryExpr.ResolvedOpcode ResolvedOpcodeForIn => BinaryExpr.ResolvedOpcode.InMultiSet;
  public override CollectionBoundedPool GetBoundedPool(Expression source) {
    return new MultiSetBoundedPool(source, Arg, Arg);
  }
}

public class SeqType : CollectionType {
  public SeqType(Type arg) : base(arg) {
  }
  public override string CollectionTypeName { get { return "seq"; } }
  public override bool Equals(Type that, bool keepConstraints = false) {
    var t = that.NormalizeExpand(keepConstraints) as SeqType;
    return t != null && Arg.Equals(t.Arg, keepConstraints);
  }

  public override Type Subst(IDictionary<TypeParameter, Type> subst) {
    var arg = Arg.Subst(subst);
    if (arg is InferredTypeProxy) {
      ((InferredTypeProxy)arg).KeepConstraints = true;
    }
    return arg == Arg ? this : new SeqType(arg);
  }

  public override Type ReplaceTypeArguments(List<Type> arguments) {
    return new SeqType(arguments[0]);
  }

  public override bool SupportsEquality {
    get {
      // The sequence type supports equality if its element type does
      return Arg.SupportsEquality;
    }
  }

  public override BinaryExpr.ResolvedOpcode ResolvedOpcodeForIn => BinaryExpr.ResolvedOpcode.InSeq;
  public override CollectionBoundedPool GetBoundedPool(Expression source) {
    return new SeqBoundedPool(source, Arg, Arg);
  }
}

public abstract class TypeProxy : Type {
  public override IEnumerable<INode> Children => Enumerable.Empty<Node>();
  [FilledInDuringResolution] public Type T;
  public readonly List<TypeConstraint> SupertypeConstraints = [];
  public readonly List<TypeConstraint> SubtypeConstraints = [];

  public override Type Subst(IDictionary<TypeParameter, Type> subst) {
    if (T == null) {
      return this;
    }
    var s = T.Subst(subst);
    return s == T ? this : s;

  }

  public override Type ReplaceTypeArguments(List<Type> arguments) {
    throw new NotSupportedException();
  }

  public IEnumerable<Type> Supertypes {
    get {
      foreach (var c in SupertypeConstraints) {
        if (c.KeepConstraints) {
          yield return c.Super.NormalizeExpandKeepConstraints();
        } else {
          yield return c.Super.NormalizeExpand();
        }
      }
    }
  }
  public IEnumerable<Type> SupertypesKeepConstraints {
    get {
      foreach (var c in SupertypeConstraints) {
        yield return c.Super.NormalizeExpandKeepConstraints();
      }
    }
  }

  public void AddSupertype(TypeConstraint c) {
    Contract.Requires(c != null);
    Contract.Requires(c.Sub == this);
    SupertypeConstraints.Add(c);
  }
  public IEnumerable<Type> Subtypes {
    get {
      foreach (var c in SubtypeConstraints) {
        if (c.KeepConstraints) {
          yield return c.Sub.NormalizeExpandKeepConstraints();
        } else {
          yield return c.Sub.NormalizeExpand();
        }
      }
    }
  }

  public IEnumerable<Type> SubtypesKeepConstraints {
    get {
      foreach (var c in SubtypeConstraints) {
        yield return c.Sub.NormalizeExpandKeepConstraints();
      }
    }
  }

  public IEnumerable<Type> SubtypesKeepConstraints_WithAssignable(List<XConstraint> allXConstraints) {
    Contract.Requires(allXConstraints != null);
    foreach (var c in SubtypeConstraints) {
      yield return c.Sub.NormalizeExpandKeepConstraints();
    }
    foreach (var xc in allXConstraints) {
      if (xc.ConstraintName == "Assignable") {
        if (xc.Types[0].Normalize() == this) {
          yield return xc.Types[1].NormalizeExpandKeepConstraints();
        }
      }
    }
  }

  public void AddSubtype(TypeConstraint c) {
    Contract.Requires(c != null);
    Contract.Requires(c.Super == this);
    SubtypeConstraints.Add(c);
  }

  public enum Family { Unknown, Bool, Char, IntLike, RealLike, Ordinal, BitVector, ValueType, Ref, Opaque }
  public Family family = Family.Unknown;
  public static Family GetFamily(Type t) {
    Contract.Ensures(Contract.Result<Family>() != Family.Unknown || t is TypeProxy || t is ResolverIdentifierExpr.ResolverType);  // return Unknown ==> t is TypeProxy || t is ResolverType
    if (t.IsBoolType) {
      return Family.Bool;
    } else if (t.IsCharType) {
      return Family.Char;
    } else if (t.IsNumericBased(NumericPersuasion.Int) || t is IntVarietiesSupertype) {
      return Family.IntLike;
    } else if (t.IsNumericBased(NumericPersuasion.Real) || t is RealVarietiesSupertype) {
      return Family.RealLike;
    } else if (t.IsBigOrdinalType) {
      return Family.Ordinal;
    } else if (t.IsBitVectorType) {
      return Family.BitVector;
    } else if (t.AsCollectionType != null || t.AsArrowType != null || t.IsDatatype) {
      return Family.ValueType;
    } else if (t.IsRefType) {
      return Family.Ref;
    } else if (t.IsTypeParameter || t.IsAbstractType || t.IsInternalTypeSynonym) {
      return Family.Opaque;
    } else if (t is TypeProxy) {
      return ((TypeProxy)t).family;
    } else {
      return Family.Unknown;
    }
  }

  internal TypeProxy() {
  }

#if TI_DEBUG_PRINT
  static int _id = 0;
  int id = _id++;
#endif
  [System.Diagnostics.Contracts.Pure]
  public override string TypeName(DafnyOptions options, ModuleDefinition context, bool parseAble) {
    Contract.Ensures(Contract.Result<string>() != null);
#if TI_DEBUG_PRINT
    if (options.Get(CommonOptionBag.TypeInferenceDebug)) {
      return T == null ? "?" + id : T.TypeName(options, context);
    }
#endif
    return T == null ? "?" : T.TypeName(options, context, parseAble);
  }
  public override bool SupportsEquality {
    get {
      if (T != null) {
        return T.SupportsEquality;
      } else {
        return base.SupportsEquality;
      }
    }
  }
  public override bool ComputeMayInvolveReferences(ISet<DatatypeDecl> visitedDatatypes) {
    if (T != null) {
      return T.ComputeMayInvolveReferences(visitedDatatypes);
    } else {
      return true;
    }
  }
  public override bool Equals(Type that, bool keepConstraints = false) {
    var i = NormalizeExpand(keepConstraints);
    if (i is TypeProxy) {
      var u = that.NormalizeExpand(keepConstraints) as TypeProxy;
      return u != null && object.ReferenceEquals(i, u);
    } else {
      return i.Equals(that, keepConstraints);
    }
  }

  [System.Diagnostics.Contracts.Pure]
  internal static bool IsSupertypeOfLiteral(Type t) {
    Contract.Requires(t != null);
    return t is ArtificialType;
  }
  internal Type InClusterOfArtificial(List<XConstraint> allXConstraints) {
    Contract.Requires(allXConstraints != null);
    return InClusterOfArtificial_aux(new HashSet<TypeProxy>(), allXConstraints);
  }
  private Type InClusterOfArtificial_aux(ISet<TypeProxy> visitedProxies, List<XConstraint> allXConstraints) {
    Contract.Requires(visitedProxies != null);
    Contract.Requires(allXConstraints != null);
    if (visitedProxies.Contains(this)) {
      return null;
    }
    visitedProxies.Add(this);
    foreach (var c in SupertypeConstraints) {
      var sup = c.Super.Normalize();
      if (sup is IntVarietiesSupertype) {
        return Type.Int;
      } else if (sup is RealVarietiesSupertype) {
        return Type.Real;
      } else if (sup is TypeProxy) {
        var a = ((TypeProxy)sup).InClusterOfArtificial_aux(visitedProxies, allXConstraints);
        if (a != null) {
          return a;
        }
      }
    }
    foreach (var su in SubtypesKeepConstraints_WithAssignable(allXConstraints)) {
      var pr = su as TypeProxy;
      if (pr != null) {
        var a = pr.InClusterOfArtificial_aux(visitedProxies, allXConstraints);
        if (a != null) {
          return a;
        }
      }
    }
    return null;
  }
}

/// <summary>
/// This proxy stands for any type.
/// </summary>
public class InferredTypeProxy : TypeProxy {
  public bool KeepConstraints;
  public InferredTypeProxy() : base() {
    KeepConstraints = false; // whether the typeProxy should be inferred to base type or as subset type
  }
}

/// <summary>
/// This proxy stands for any type, but it originates from an instantiated type parameter.
/// </summary>
public class ParamTypeProxy : TypeProxy {
  public override IEnumerable<INode> Children => Enumerable.Empty<Node>();
  public TypeParameter orig;
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(orig != null);
  }

  public ParamTypeProxy(TypeParameter orig) {
    Contract.Requires(orig != null);
    this.orig = orig;
  }
}
