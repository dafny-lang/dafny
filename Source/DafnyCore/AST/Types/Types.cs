#define TI_DEBUG_PRINT
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Threading;

namespace Microsoft.Dafny;

public abstract class Type : NodeWithOrigin {
  public static BoolType Bool = new BoolType();
  public static CharType Char = new CharType();
  public static IntType Int = new IntType();
  public static RealType Real = new RealType();
  public static FieldType Field = new FieldType();

  [SyntaxConstructor]
  protected Type(IOrigin origin = null) : base(origin) {
  }

  protected Type(Cloner cloner, Type original) : base(cloner, original) {
  }

  public override IEnumerable<INode> Children => TypeArgs;
  public override IEnumerable<INode> PreResolveChildren => TypeArgs.OfType<Node>();
  public static Type Nat() { return new UserDefinedType(Token.NoToken, "nat", null); }  // note, this returns an unresolved type
  public static Type String() { return new UserDefinedType(Token.NoToken, "string", null); }  // note, this returns an unresolved type

  public static Type ResolvedString() {
    return new SeqType(new CharType());
  }

  public static BigOrdinalType BigOrdinal = new();

  private static ThreadLocal<List<VisibilityScope>> _scopes = new();
  private static List<VisibilityScope> Scopes => _scopes.Value ??= [];

  [ThreadStatic]
  private static bool scopesEnabled;

  public virtual IEnumerable<Node> Nodes => [];

  public static void PushScope(VisibilityScope scope) {
    Scopes.Add(scope);
  }

  public static void ResetScopes() {
    _scopes.Value = [];
    scopesEnabled = false;
  }

  public static void PopScope() {
    Contract.Assert(Scopes.Count > 0);
    Scopes.RemoveAt(Scopes.Count - 1);
  }

  public static void PopScope(VisibilityScope expected) {
    Contract.Assert(Scopes.Count > 0);
    Contract.Assert(Scopes[^1] == expected);
    PopScope();
  }

  public static VisibilityScope GetScope() {
    if (scopesEnabled && Scopes.Count > 0) {
      return Scopes[^1];
    }
    return null;
  }

  public static void EnableScopes() {
    Contract.Assert(!scopesEnabled);
    scopesEnabled = true;
  }

  public static void DisableScopes() {
    Contract.Assert(scopesEnabled);
    scopesEnabled = false;
  }

  public static string TypeArgsToString(DafnyOptions options, ModuleDefinition/*?*/ context, List<Type> typeArgs, bool parseAble = false) {
    Contract.Requires(typeArgs == null ||
                      (typeArgs.All(ty => ty != null && ty.TypeName(options, context, parseAble) != null) &&
                       (typeArgs.All(ty => ty.TypeName(options, context, parseAble).StartsWith("_")) ||
                        typeArgs.All(ty => !ty.TypeName(options, context, parseAble).StartsWith("_")))));

    if (typeArgs != null && typeArgs.Count > 0 &&
        (!parseAble || !typeArgs[0].TypeName(options, context, parseAble).StartsWith("_"))) {
      return string.Format("<{0}>", Util.Comma(typeArgs, ty => ty.TypeName(options, context, parseAble)));
    }
    return "";
  }

  public static string TypeArgsToString(DafnyOptions options, List<Type> typeArgs, bool parseAble = false) {
    return TypeArgsToString(options, null, typeArgs, parseAble);
  }

  public string TypeArgsToString(DafnyOptions options, ModuleDefinition/*?*/ context, bool parseAble = false) {
    return Type.TypeArgsToString(options, context, this.TypeArgs, parseAble);
  }

  // Type arguments to the type
  public virtual List<Type> TypeArgs { get; set; } = [];

  /// <summary>
  /// Add to "tps" the free type parameters in "this".
  /// Requires the type to be resolved.
  /// </summary>
  public void AddFreeTypeParameters(ISet<TypeParameter> tps) {
    Contract.Requires(tps != null);
    var ty = this.NormalizeExpandKeepConstraints();
    if (ty.AsTypeParameter is { } tp) {
      tps.Add(tp);
    }
    foreach (var ta in ty.TypeArgs) {
      ta.AddFreeTypeParameters(tps);
    }
  }

  [System.Diagnostics.Contracts.Pure]
  public abstract string TypeName(DafnyOptions options, ModuleDefinition/*?*/ context, bool parseAble = false);

  [System.Diagnostics.Contracts.Pure]
  public override string ToString() {
    return TypeName(DafnyOptions.DefaultImmutableOptions, null, false);
  }

  /// <summary>
  /// Return the most constrained version of "this", getting to the bottom of proxies.
  ///
  /// Here is a description of the Normalize(), NormalizeExpandKeepConstraints(), and NormalizeExpand() methods:
  /// * Any .Type field in the AST can, in general, be an AST node that is not really a type, but an AST node that has
  ///   a field where the type is filled in, once the type has been inferred. Such "types" are called "type proxies".
  ///   To follow a .Type (or other variable denoting a type) past its chain of type proxies, you call .Normalize().
  ///   If you do this after type inference (more precisely, after the CheckTypeInference calls in Pass 1 of the
  ///   Resolver), then you will get back a NonProxyType.
  /// * That may not be enough. Even after calling .Normalize(), you may get a type that denotes a type synonym. If
  ///   you compare it with, say, is SetType, you will get false if the type you're looking at is a type synonym for
  ///   a SetType. Therefore, to go past both type proxies and type synonyms, you call .NormalizeExpandKeepConstraints().
  /// * Actually, that may not be enough, either. Because .NormalizeExpandKeepConstraints() may return a subset type
  ///   whose base type is what you're looking for. If you want to go all the way to the base type, then you should
  ///   call .NormalizeExpand(). This is what is done most commonly when something is trying to look for a specific type.
  /// * So, in conclusion: Usually you have to call .NormalizeExpand() on a type to unravel type proxies, type synonyms,
  ///   and subset types. But in other places (in particular, in the verifier) where you want to know about any type
  ///   constraints, then you call .NormalizeExpandKeepConstraints().
  /// </summary>
  public Type Normalize() {
    Contract.Ensures(Contract.Result<Type>() != null);
    Type type = this;
    while (true) {
      if (type is TypeProxy { T: { } proxyTarget }) {
        type = proxyTarget;
      } else {
        return type;
      }
    }
  }

  /// <summary>
  /// Return the type that "this" stands for, getting to the bottom of proxies, and then using an InternalTypeSynonym if
  /// the type is not in scope.
  ///
  /// For more documentation, see method Normalize().
  /// </summary>
  [System.Diagnostics.Contracts.Pure]
  public Type NormalizeAndAdjustForScope() {
    return NormalizeExpand(ExpandMode.DontExpandJustAdjustForScopes);
  }

  /// <summary>
  /// Call NormalizeExpand() repeatedly, also on the base type of newtype's.
  /// </summary>
  public Type NormalizeToAncestorType() {
    Type result = this;
    while (true) {
      result = result.NormalizeExpand();
      if (result.AsNewtype is { } newtypeDecl) {
        result = newtypeDecl.ConcreteBaseType(result.TypeArgs);
      } else {
        return result;
      }
    }
  }

  /// <summary>
  /// Return the type that "this" stands for, getting to the bottom of proxies and following type synonyms, but does
  /// not follow subset types.
  ///
  /// For more documentation, see method Normalize().
  /// </summary>
  [System.Diagnostics.Contracts.Pure]
  public Type NormalizeExpandKeepConstraints() {
    return NormalizeExpand(ExpandMode.ExpandSynonymsOnly);
  }

  public Type NormalizeExpand(bool keepConstraints) {
    return NormalizeExpand(keepConstraints ? ExpandMode.ExpandSynonymsOnly : ExpandMode.ExpandSynonymsAndSubsetTypes);
  }

  public enum ExpandMode {
    DontExpandJustAdjustForScopes,
    ExpandSynonymsOnly,
    ExpandSynonymsAndSubsetTypes
  }

  public NativeType AsNativeType() {
    if (AsNewtype != null) {
      return AsNewtype.NativeType;
    } else if (IsBitVectorType) {
      return AsBitVectorType.NativeType;
    }
    return null;
  }

  /// <summary>
  /// Return the type that "this" stands for, getting to the bottom of proxies and following type synonyms.
  ///
  /// For more documentation, see method Normalize().
  /// </summary>
  [System.Diagnostics.Contracts.Pure]
  public Type NormalizeExpand(ExpandMode expandMode = ExpandMode.ExpandSynonymsAndSubsetTypes) {
    Contract.Ensures(Contract.Result<Type>() != null);
    Contract.Ensures(!(Contract.Result<Type>() is TypeProxy) || ((TypeProxy)Contract.Result<Type>()).T == null);  // return a proxy only if .T == null

    Type type = this;
    while (true) {
      if (type is TypeProxy { T: not null } pt) {
        type = pt.T;
        continue;
      }

      var scope = Type.GetScope();
      var rtd = type.AsRevealableType;
      if (rtd != null) {
        var udt = (UserDefinedType)type;

        if (!rtd.AsTopLevelDecl.IsVisibleInScope(scope)) {
          // This can only mean "rtd" is a class/trait that is only provided, not revealed. For a provided class/trait,
          // it is the non-null type declaration that is visible, not the class/trait declaration itself.
          if (rtd is ClassLikeDecl cl) {
            Contract.Assert(cl.NonNullTypeDecl != null);
            Contract.Assert(cl.NonNullTypeDecl.IsVisibleInScope(scope));
          } else {
            Contract.Assert(rtd is AbstractTypeDecl);
          }
        }

        if (rtd.IsRevealedInScope(scope)) {
          if (expandMode != ExpandMode.DontExpandJustAdjustForScopes && rtd is TypeSynonymDecl typeSynonymDecl) {
            if (typeSynonymDecl is not SubsetTypeDecl || expandMode == ExpandMode.ExpandSynonymsAndSubsetTypes) {
              type = typeSynonymDecl.RhsWithArgumentIgnoringScope(udt.TypeArgs);
              continue;
            }
          }
          return type;
        } else { // type is hidden, no more normalization is possible
          return rtd.SelfSynonym(type.TypeArgs);
        }
      }

      // A hidden type may become visible in another scope
      var isyn = type.AsInternalTypeSynonym;
      if (isyn != null) {
        var udt = (UserDefinedType)type;

        if (!isyn.IsVisibleInScope(scope)) {
          // This can only mean "isyn" refers to a class/trait that is only provided, not revealed. For a provided class/trait,
          // it is the non-null type declaration that is visible, not the class/trait declaration itself.
          var rhs = isyn.RhsWithArgumentIgnoringScope(udt.TypeArgs);
          Contract.Assert(rhs is UserDefinedType);
          var cl = ((UserDefinedType)rhs).ResolvedClass as ClassLikeDecl;
          Contract.Assert(cl != null && cl.NonNullTypeDecl != null, rhs.ToString());
          Contract.Assert(cl.NonNullTypeDecl.IsVisibleInScope(scope));
        }

        if (isyn.IsRevealedInScope(scope)) {
          type = isyn.RhsWithArgument(udt.TypeArgs);
          continue;
        } else {
          return type;
        }
      }

      return type;
    }
  }

  /// <summary>
  /// Return "the type that "this" stands for, getting to the bottom of proxies and following type synonyms.
  /// </summary>
  public Type UseInternalSynonym() {
    Contract.Ensures(Contract.Result<Type>() != null);
    Contract.Ensures(!(Contract.Result<Type>() is TypeProxy) || ((TypeProxy)Contract.Result<Type>()).T == null);  // return a proxy only if .T == null

    Type type = Normalize();
    var scope = Type.GetScope();
    var rtd = type.AsRevealableType;
    if (rtd != null) {
      var udt = (UserDefinedType)type;
      if (!rtd.AsTopLevelDecl.IsVisibleInScope(scope)) {
        // This can only mean "rtd" is a class/trait that is only provided, not revealed. For a provided class/trait,
        // it is the non-null type declaration that is visible, not the class/trait declaration itself.
        var cl = rtd as ClassLikeDecl;
        Contract.Assert(cl != null && cl.NonNullTypeDecl != null);
        Contract.Assert(cl.NonNullTypeDecl.IsVisibleInScope(scope));
      }
      if (!rtd.IsRevealedInScope(scope)) {
        return rtd.SelfSynonym(type.TypeArgs, udt.NamePath);
      }
    }

    return type;
  }

  /// <summary>
  /// Return a type that is like "this", but where occurrences of type parameters are substituted as indicated by "subst".
  /// </summary>
  public abstract Type Subst(IDictionary<TypeParameter, Type> subst);

  /// <summary>
  /// Return a type that is like "type", but with type arguments "arguments".
  /// </summary>
  public abstract Type ReplaceTypeArguments(List<Type> arguments);

  /// <summary>
  /// Returns whether or not "this" and "that" denote the same type, modulo proxies and type synonyms and subset types.
  /// </summary>
  [System.Diagnostics.Contracts.Pure]
  public abstract bool Equals(Type that, bool keepConstraints = false);

  public bool IsBoolType => NormalizeExpand() is BoolType;
  public bool IsCharType => NormalizeExpand() is CharType;
  public bool IsIntegerType => NormalizeExpand() is IntType;
  public bool IsRealType => NormalizeExpand() is RealType;
  public bool IsBigOrdinalType => NormalizeExpand() is BigOrdinalType;
  public bool IsBitVectorType => AsBitVectorType != null;
  public bool IsStringType => AsSeqType?.Arg.IsCharType == true;
  public BitvectorType AsBitVectorType => NormalizeExpand() as BitvectorType;

  public bool IsNumericBased() {
    var t = NormalizeExpand();
    return t.IsIntegerType || t.IsRealType || t.AsNewtype?.BaseType.IsNumericBased() == true;
  }
  public enum NumericPersuasion { Int, Real }
  [System.Diagnostics.Contracts.Pure]
  public bool IsNumericBased(NumericPersuasion p) {
    Type t = this;
    while (true) {
      t = t.NormalizeExpand();
      if (t.IsIntegerType) {
        return p == NumericPersuasion.Int;
      } else if (t.IsRealType) {
        return p == NumericPersuasion.Real;
      }
      if (t.AsNewtype is not { } newtypeDecl) {
        return false;
      }
      t = newtypeDecl.RhsWithArgument(t.TypeArgs);
    }
  }

  /// <summary>
  /// Returns true if the type has two representations at run time, the ordinary representation and a
  /// "fat pointer" representation (which is a boxing of the ordinary representation, plus a vtable pointer).
  /// </summary>
  public bool HasFatPointer => NormalizeExpand() is UserDefinedType { ResolvedClass: NewtypeDecl { Traits: { Count: > 0 } } };

  /// <summary>
  /// This property returns true if the type is known to be nonempty.
  /// This property should be used only after successful resolution. It is assumed that all type proxies have
  /// been resolved and that all recursion through types comes to an end.
  /// Note, HasCompilableValue ==> IsNonEmpty.
  /// </summary>
  public bool IsNonempty => GetAutoInit() != AutoInitInfo.MaybeEmpty;

  /// <summary>
  /// This property returns true if the type has a known compilable value.
  /// This property should be used only after successful resolution. It is assumed that all type proxies have
  /// been resolved and that all recursion through types comes to an end.
  /// Note, HasCompilableValue ==> IsNonEmpty.
  /// </summary>
  public bool HasCompilableValue => GetAutoInit() == AutoInitInfo.CompilableValue;

  public bool KnownToHaveToAValue(bool ghostContext) {
    return ghostContext ? IsNonempty : HasCompilableValue;
  }

  public enum AutoInitInfo { MaybeEmpty, Nonempty, CompilableValue }

  public bool HavocCountsAsDefiniteAssignment(bool inGhostContext) {
    return inGhostContext ? IsNonempty : HasCompilableValue;
  }

  /// <summary>
  /// This property returns
  ///     - CompilableValue, if the type has a known compilable value
  ///     - Nonempty,        if the type is known to contain some value
  ///     - MaybeEmpty,      otherwise
  /// This property should be used only after successful resolution. It is assumed that all type proxies have
  /// been resolved and that all recursion through types comes to an end.
  /// </summary>
  public AutoInitInfo GetAutoInit(List<UserDefinedType>/*?*/ coDatatypesBeingVisited = null) {
    var t = NormalizeExpandKeepConstraints();
    Contract.Assume(t is NonProxyType); // precondition

    AutoInitInfo CharacteristicToAutoInitInfo(TypeParameterCharacteristics c) {
      if (c.HasCompiledValue) {
        return AutoInitInfo.CompilableValue;
      } else if (c.IsNonempty) {
        return AutoInitInfo.Nonempty;
      } else {
        return AutoInitInfo.MaybeEmpty;
      }
    }

    if (t is BoolType || t is CharType || t is IntType || t is BigOrdinalType || t is RealType || t is BitvectorType) {
      return AutoInitInfo.CompilableValue;
    } else if (t is CollectionType) {
      return AutoInitInfo.CompilableValue;
    } else if (t is FieldType) {
      return AutoInitInfo.MaybeEmpty;
    }

    var udt = (UserDefinedType)t;
    var cl = udt.ResolvedClass;
    Contract.Assert(cl != null);
    if (cl is AbstractTypeDecl) {
      var otd = (AbstractTypeDecl)cl;
      return CharacteristicToAutoInitInfo(otd.Characteristics);
    } else if (cl is TypeParameter) {
      var tp = (TypeParameter)cl;
      return CharacteristicToAutoInitInfo(tp.Characteristics);
    } else if (cl is InternalTypeSynonymDecl) {
      var isyn = (InternalTypeSynonymDecl)cl;
      return CharacteristicToAutoInitInfo(isyn.Characteristics);
    } else if (cl is NewtypeDecl) {
      var td = (NewtypeDecl)cl;
      switch (td.WitnessKind) {
        case SubsetTypeDecl.WKind.CompiledZero:
        case SubsetTypeDecl.WKind.Compiled:
          return AutoInitInfo.CompilableValue;
        case SubsetTypeDecl.WKind.Ghost:
          return AutoInitInfo.Nonempty;
        case SubsetTypeDecl.WKind.OptOut:
          return AutoInitInfo.MaybeEmpty;
        case SubsetTypeDecl.WKind.Special:
        default:
          Contract.Assert(false); // unexpected case
          throw new Cce.UnreachableException();
      }
    } else if (cl is SubsetTypeDecl) {
      var td = (SubsetTypeDecl)cl;
      switch (td.WitnessKind) {
        case SubsetTypeDecl.WKind.CompiledZero:
        case SubsetTypeDecl.WKind.Compiled:
          return AutoInitInfo.CompilableValue;
        case SubsetTypeDecl.WKind.Ghost:
          return AutoInitInfo.Nonempty;
        case SubsetTypeDecl.WKind.OptOut:
          return AutoInitInfo.MaybeEmpty;
        case SubsetTypeDecl.WKind.Special:
          // WKind.Special is only used with -->, ->, and non-null types:
          Contract.Assert(ArrowType.IsPartialArrowTypeName(td.Name) || ArrowType.IsTotalArrowTypeName(td.Name) || td is NonNullTypeDecl);
          if (ArrowType.IsPartialArrowTypeName(td.Name)) {
            // partial arrow
            return AutoInitInfo.CompilableValue;
          } else if (ArrowType.IsTotalArrowTypeName(td.Name)) {
            // total arrow
            return udt.TypeArgs.Last().GetAutoInit(coDatatypesBeingVisited);
          } else if (((NonNullTypeDecl)td).Class is ArrayClassDecl) {
            // non-null array type; we know how to initialize them
            return AutoInitInfo.CompilableValue;
          } else {
            // non-null (non-array) type
            return AutoInitInfo.MaybeEmpty;
          }
        default:
          Contract.Assert(false); // unexpected case
          throw new Cce.UnreachableException();
      }
    } else if (cl is TraitDecl traitDecl) {
      return traitDecl.IsReferenceTypeDecl ? AutoInitInfo.CompilableValue : AutoInitInfo.MaybeEmpty;
    } else if (cl is ClassDecl) {
      return AutoInitInfo.CompilableValue; // null is a value of this type
    } else if (cl is ArrowTypeDecl) {
      return AutoInitInfo.CompilableValue;
    } else if (cl is DatatypeDecl) {
      var dt = (DatatypeDecl)cl;
      var subst = TypeParameter.SubstitutionMap(dt.TypeArgs, udt.TypeArgs);
      var r = AutoInitInfo.CompilableValue;  // assume it's compilable, until we find out otherwise
      if (cl is CoDatatypeDecl) {
        if (coDatatypesBeingVisited != null) {
          if (coDatatypesBeingVisited.Exists(coType => udt.Equals(coType))) {
            // This can be compiled into a lazy constructor call
            return AutoInitInfo.CompilableValue;
          } else if (coDatatypesBeingVisited.Exists(coType => dt == coType.ResolvedClass)) {
            // This requires more recursion and bookkeeping than we care to try out
            return AutoInitInfo.MaybeEmpty;
          }
          coDatatypesBeingVisited = [.. coDatatypesBeingVisited];
        } else {
          coDatatypesBeingVisited = [];
        }
        coDatatypesBeingVisited.Add(udt);
      }
      foreach (var formal in dt.GetGroundingCtor().Formals) {
        var autoInit = formal.Type.Subst(subst).GetAutoInit(coDatatypesBeingVisited);
        if (autoInit == AutoInitInfo.MaybeEmpty) {
          return AutoInitInfo.MaybeEmpty;
        } else if (formal.IsGhost) {
          // cool
        } else if (autoInit == AutoInitInfo.CompilableValue) {
          // cool
        } else {
          r = AutoInitInfo.Nonempty;
        }
      }
      return r;
    } else {
      Contract.Assert(false); // unexpected type
      throw new Cce.UnreachableException();
    }
  }

  public bool HasFinitePossibleValues {
    get {
      if (IsBoolType || IsCharType || IsRefType) {
        return true;
      }
      var st = AsSetType;
      if (st != null && st.Arg.HasFinitePossibleValues) {
        return true;
      }
      var mt = AsMapType;
      if (mt != null && mt.Domain.HasFinitePossibleValues) {
        return true;
      }
      var dt = AsDatatype;
      if (dt != null && dt.HasFinitePossibleValues) {
        return true;
      }
      return false;
    }
  }

  public CollectionType AsCollectionType { get { return NormalizeExpand() as CollectionType; } }
  public SetType AsSetType { get { return NormalizeExpand() as SetType; } }
  public MultiSetType AsMultiSetType { get { return NormalizeExpand() as MultiSetType; } }
  public SeqType AsSeqType { get { return NormalizeExpand() as SeqType; } }
  public MapType AsMapType { get { return NormalizeExpand() as MapType; } }

  public bool IsRefType {
    get {
      return NormalizeExpand() is UserDefinedType { ResolvedClass: ClassLikeDecl { IsReferenceTypeDecl: true } };
    }
  }

  public bool IsMemoryLocationType {
    get {
      return NormalizeExpand() is UserDefinedType {
        ResolvedClass: TupleTypeDecl { Dims: 2 },
        TypeArgs: var typeArgs,
      }
             && typeArgs.Count == 2 && typeArgs[0].IsRefType && typeArgs[1] is FieldType;
    }
  }

  public bool IsTopLevelTypeWithMembers {
    get {
      return AsTopLevelTypeWithMembers != null;
    }
  }
  public TopLevelDeclWithMembers/*?*/ AsTopLevelTypeWithMembers {
    get {
      var udt = NormalizeExpand() as UserDefinedType;
      return udt?.ResolvedClass as TopLevelDeclWithMembers;
    }
  }
  public TopLevelDeclWithMembers/*?*/ AsTopLevelTypeWithMembersBypassInternalSynonym {
    get {
      var udt = NormalizeExpand() as UserDefinedType;
      if (udt != null && udt.ResolvedClass is InternalTypeSynonymDecl isyn) {
        udt = isyn.RhsWithArgumentIgnoringScope(udt.TypeArgs) as UserDefinedType;
        if (udt?.ResolvedClass is NonNullTypeDecl nntd) {
          return nntd.Class;
        }
      }
      return udt?.ResolvedClass as TopLevelDeclWithMembers;
    }
  }
  /// <summary>
  /// Returns "true" if the type represents the type "object?".
  /// </summary>
  public bool IsObjectQ {
    get {
      return NormalizeExpandKeepConstraints() is UserDefinedType { ResolvedClass: TraitDecl { IsObjectTrait: true } };
    }
  }
  /// <summary>
  /// Returns "true" if the type represents the type "object".
  /// </summary>
  public bool IsObject {
    get {
      var nn = AsNonNullRefType;
      if (nn != null) {
        var nonNullRefDecl = (NonNullTypeDecl)nn.ResolvedClass;
        return nonNullRefDecl.Class is TraitDecl { IsObjectTrait: true };
      }
      return false;
    }
  }
  /// <summary>
  /// Returns "true" if the type is a non-null type or any subset type thereof.
  /// </summary>
  public bool IsNonNullRefType {
    get {
      return AsNonNullRefType != null;
    }
  }
  /// <summary>
  /// If the type is a non-null type or any subset type thereof, return the UserDefinedType whose
  /// .ResolvedClass value is a NonNullTypeDecl.
  /// Otherwise, return "null".
  /// </summary>
  public UserDefinedType AsNonNullRefType {
    get {
      var t = this;
      while (true) {
        if (t.NormalizeExpandKeepConstraints() is not UserDefinedType udt) {
          return null;
        }
        if (udt.ResolvedClass is NonNullTypeDecl) {
          return udt;
        }
        if (udt.ResolvedClass is SubsetTypeDecl sst) {
          t = sst.RhsWithArgument(udt.TypeArgs);  // continue the search up the chain of subset types
        } else {
          return null;
        }
      }
    }
  }
  /// <summary>
  /// Returns the type "parent<X>", where "X" is a list of type parameters that makes "parent<X>" a supertype of "this".
  /// Requires "this" to be some type "C<Y>" and "parent" to be among the reflexive, transitive parent traits of "C".
  /// </summary>
  public UserDefinedType AsParentType(TopLevelDecl parent) {
    Contract.Requires(parent != null);

    var udt = (UserDefinedType)NormalizeExpand();
    if (udt.ResolvedClass is InternalTypeSynonymDecl isyn) {
      udt = (UserDefinedType)isyn.RhsWithArgumentIgnoringScope(udt.TypeArgs);
    }
    TopLevelDeclWithMembers cl;
    if (udt.ResolvedClass is NonNullTypeDecl nntd) {
      cl = (TopLevelDeclWithMembers)nntd.ViewAsClass;
    } else {
      cl = (TopLevelDeclWithMembers)udt.ResolvedClass;
    }
    if (cl == parent) {
      return udt;
    }
    var typeMapParents = cl.ParentFormalTypeParametersToActuals;
    var typeMapUdt = TypeParameter.SubstitutionMap(cl.TypeArgs, udt.TypeArgs);
    var typeArgs = parent.TypeArgs.ConvertAll(tp => typeMapParents[tp].Subst(typeMapUdt));
    return new UserDefinedType(udt.Origin, parent.Name, parent, typeArgs);
  }

  public bool IsTraitType => AsTraitType != null;
  public TraitDecl/*?*/ AsTraitType {
    get {
      var udt = NormalizeExpand() as UserDefinedType;
      return udt?.ResolvedClass as TraitDecl;
    }
  }

  public SubsetTypeDecl /*?*/ AsSubsetType {
    get {
      var std = NormalizeExpand(true) as UserDefinedType;
      return std?.ResolvedClass as SubsetTypeDecl;
    }
  }

  public bool IsArrayType {
    get {
      return AsArrayType != null;
    }
  }
  public ArrayClassDecl/*?*/ AsArrayType {
    get {
      var udt = UserDefinedType.DenotesClass(this);
      return udt?.ResolvedClass as ArrayClassDecl;
    }
  }
  /// <summary>
  /// Returns "true" if the type is one of the 3 built-in arrow types.
  /// </summary>
  public bool IsBuiltinArrowType {
    get {
      var t = Normalize();  // but don't expand synonyms or strip off constraints
      if (t is ArrowType) {
        return true;
      }
      var udt = t as UserDefinedType;
      return udt != null && (ArrowType.IsPartialArrowTypeName(udt.Name) || ArrowType.IsTotalArrowTypeName(udt.Name));
    }
  }
  /// <summary>
  /// Returns "true" if the type is a partial arrow or any subset type thereof.
  /// </summary>
  public bool IsArrowTypeWithoutReadEffects {
    get {
      var t = this;
      while (true) {
        var udt = t.NormalizeExpandKeepConstraints() as UserDefinedType;
        if (udt == null) {
          return false;
        } else if (ArrowType.IsPartialArrowTypeName(udt.Name)) {
          return true;
        }
        var sst = udt.ResolvedClass as SubsetTypeDecl;
        if (sst != null) {
          t = sst.RhsWithArgument(udt.TypeArgs);  // continue the search up the chain of subset types
        } else {
          return false;
        }
      }
    }
  }
  /// <summary>
  /// Returns "true" if the type is a total arrow or any subset type thereof.
  /// </summary>
  public bool IsArrowTypeWithoutPreconditions {
    get {
      var t = this;
      while (true) {
        var udt = t.NormalizeExpandKeepConstraints() as UserDefinedType;
        if (udt == null) {
          return false;
        } else if (ArrowType.IsTotalArrowTypeName(udt.Name)) {
          return true;
        }
        var sst = udt.ResolvedClass as SubsetTypeDecl;
        if (sst != null) {
          t = sst.RhsWithArgument(udt.TypeArgs);  // continue the search up the chain of subset types
        } else {
          return false;
        }
      }
    }
  }
  public bool IsArrowType => AsArrowType != null;

  public ArrowType AsArrowType => NormalizeExpand() as ArrowType;

  public bool IsMapType => NormalizeExpand() is MapType { Finite: true };

  public bool IsIMapType => NormalizeExpand() is MapType { Finite: false };

  public bool IsISetType => NormalizeExpand() is SetType { Finite: false };

  public NewtypeDecl AsNewtype {
    get {
      var udt = NormalizeExpand() as UserDefinedType;
      return udt?.ResolvedClass as NewtypeDecl;
    }
  }
  public TypeSynonymDecl AsTypeSynonym {
    get {
      var udt = this as UserDefinedType;  // note, it is important to use 'this' here, not 'this.NormalizeExpand()'
      return udt?.ResolvedClass as TypeSynonymDecl;
    }
  }
  public InternalTypeSynonymDecl AsInternalTypeSynonym {
    get {
      var udt = this as UserDefinedType;  // note, it is important to use 'this' here, not 'this.NormalizeExpand()'
      return udt?.ResolvedClass as InternalTypeSynonymDecl;
    }
  }
  public RedirectingTypeDecl AsRedirectingType {
    get {
      var udt = this as UserDefinedType;  // Note, it is important to use 'this' here, not 'this.NormalizeExpand()'.  This property getter is intended to be used during resolution, or with care thereafter.
      if (udt == null) {
        return null;
      } else {
        return (RedirectingTypeDecl)(udt.ResolvedClass as TypeSynonymDecl) ?? udt.ResolvedClass as NewtypeDecl;
      }
    }
  }
  public RevealableTypeDecl AsRevealableType {
    get {
      var udt = this as UserDefinedType;
      return udt?.ResolvedClass as RevealableTypeDecl;
    }
  }
  public bool IsRevealableType => AsRevealableType != null;

  public bool IsDatatype => AsDatatype != null;

  public DatatypeDecl AsDatatype {
    get {
      var udt = NormalizeExpand() as UserDefinedType;
      return udt?.ResolvedClass as DatatypeDecl;
    }
  }
  public bool IsIndDatatype => AsIndDatatype != null;

  public IndDatatypeDecl AsIndDatatype {
    get {
      var udt = NormalizeExpand() as UserDefinedType;
      return udt?.ResolvedClass as IndDatatypeDecl;
    }
  }
  public bool IsCoDatatype => AsCoDatatype != null;

  public CoDatatypeDecl AsCoDatatype {
    get {
      var udt = NormalizeExpand() as UserDefinedType;
      return udt?.ResolvedClass as CoDatatypeDecl;
    }
  }
  public bool InvolvesCoDatatype {
    get {
      return IsCoDatatype;  // TODO: should really check structure of the type recursively
    }
  }
  public bool IsTypeParameter => AsTypeParameter != null;

  public bool IsInternalTypeSynonym => AsInternalTypeSynonym != null;

  public TypeParameter AsTypeParameter {
    get {
      var ct = NormalizeExpandKeepConstraints() as UserDefinedType;
      return ct?.ResolvedClass as TypeParameter;
    }
  }
  public bool IsAbstractType => AsAbstractType != null;

  public AbstractTypeDecl AsAbstractType {
    get {
      var udt = this.Normalize() as UserDefinedType;  // note, it is important to use 'this.Normalize()' here, not 'this.NormalizeExpand()'
      return udt?.ResolvedClass as AbstractTypeDecl;
    }
  }

  /// <summary>
  /// Returns whether or not any values of the type can be checked for equality in compiled contexts
  /// </summary>
  public virtual bool SupportsEquality => true;

  /// <summary>
  /// Returns whether or not some values of the type can be checked for equality in compiled contexts.
  /// This differs from SupportsEquality for types where the equality operation is partial, e.g.,
  /// for datatypes where some, but not all, constructors are ghost.
  /// Note, whereas SupportsEquality sometimes consults some constituent type for SupportEquality
  /// (e.g., seq<T> supports equality if T does), PartiallySupportsEquality does not (because the
  /// semantic check would be more complicated and it currently doesn't seem worth the trouble).
  /// </summary>
  public virtual bool PartiallySupportsEquality => SupportsEquality;

  public bool MayInvolveReferences => ComputeMayInvolveReferences(null);

  /// <summary>
  /// This is an auxiliary method used to compute the value of MayInvolveReferences (above). It is
  /// needed to handle datatypes, because determining whether or not a datatype contains references
  /// involves recursing over the types in the datatype's constructor parameters. Since those types
  /// may be mutually dependent on the datatype itself, care must be taken to avoid infinite recursion.
  ///
  /// Parameter visitedDatatypes is used to prevent infinite recursion. It is passed in as null
  /// (the "first phase") as long as no datatype has been encountered. From the time a first datatype
  /// is encountered and through all subsequent recursive calls to ComputeMayInvolveReferences that
  /// are performed on the types of the parameters of the datatype's constructors, the method enters
  /// a "second phase", where visitedDatatypes is passed in as a set that records all datatypes visited.
  /// By not recursing through a datatype that's already being visited, infinite recursion is prevented.
  ///
  /// The type parameters to recursive uses of datatypes may be passed in in different ways. In fact,
  /// there is no bound on the set of different instantiations one can encounter with the recursive uses
  /// of the datatypes. Rather than keeping track of type instantiations in (some variation of)
  /// visitedDatatypes, the type arguments passed to a datatype are checked separately. If the datatype
  /// uses all the type parameters it declares, then this will have the same effect. During the second
  /// phase, formal type parameters (which necessarily are ones declared in datatypes) are ignored.
  /// </summary>
  public abstract bool ComputeMayInvolveReferences(ISet<DatatypeDecl> /*?*/ visitedDatatypes);

  /// <summary>
  /// Returns true if it is known how to meaningfully compare the type's inhabitants.
  /// </summary>
  public bool IsOrdered {
    get {
      var ct = NormalizeExpand();
      if (ct.IsTypeParameter || ct.IsAbstractType || ct.IsInternalTypeSynonym || ct.IsCoDatatype || ct.IsArrowType || ct.IsIMapType || ct.IsISetType ||
          ct is UserDefinedType { ResolvedClass: TraitDecl { IsReferenceTypeDecl: false } }) {
        return false;
      }
      return true;
    }
  }

  /// <summary>
  /// Returns "true" iff "sub" is a subtype of "super".
  /// Expects that neither "super" nor "sub" is an unresolved proxy.
  /// </summary>
  public static bool IsSupertype(Type super, Type sub) {
    Contract.Requires(super != null);
    Contract.Requires(sub != null);
    return sub.IsSubtypeOf(super, false, false);
  }

  /// <summary>
  /// Expects that "type" has already been normalized.
  /// </summary>
  public static List<TypeParameter.TPVariance> GetPolarities(Type type) {
    Contract.Requires(type != null);
    if (type is BasicType || type is ArtificialType) {
      // there are no type parameters
      return [];
    } else if (type is MapType) {
      return [TypeParameter.TPVariance.Co, TypeParameter.TPVariance.Co];
    } else if (type is CollectionType) {
      return [TypeParameter.TPVariance.Co];
    } else {
      var udf = (UserDefinedType)type;
      if (udf.TypeArgs.Count == 0) {
        return [];
      }
      // look up the declaration of the formal type parameters
      var cl = udf.ResolvedClass;
      return cl.TypeArgs.ConvertAll(tp => tp.Variance);
    }
  }

  public static bool FromSameHead_Subtype(Type t, Type u, out Type a, out Type b) {
    Contract.Requires(t != null);
    Contract.Requires(u != null);
    if (FromSameHead(t, u, out a, out b)) {
      return true;
    }
    t = t.NormalizeExpand();
    u = u.NormalizeExpand();
    if (t.IsRefType && u.IsRefType) {
      if (t.IsObjectQ) {
        a = b = t;
        return true;
      } else if (u.IsObjectQ) {
        a = b = u;
        return true;
      }
      var tt = ((UserDefinedType)t).ResolvedClass as ClassLikeDecl;
      var uu = ((UserDefinedType)u).ResolvedClass as ClassLikeDecl;
      if (uu.HeadDerivesFrom(tt)) {
        a = b = t;
        return true;
      } else if (tt.HeadDerivesFrom(uu)) {
        a = b = u;
        return true;
      }
    }
    return false;
  }

  public static bool FromSameHead(Type t, Type u, out Type a, out Type b) {
    a = t;
    b = u;
    var towerA = GetTowerOfSubsetTypes(a);
    var towerB = GetTowerOfSubsetTypes(b);
    for (var n = Math.Min(towerA.Count, towerB.Count); 0 <= --n;) {
      a = towerA[n];
      b = towerB[n];
      if (SameHead(a, b)) {
        return true;
      }
    }
    return false;
  }

  /// <summary>
  /// Returns true if t and u have the same head type.
  /// It is assumed that t and u have been normalized and expanded by the caller, according
  /// to its purposes.
  /// The value of "allowNonNull" matters only if both "t" and "u" denote reference types.
  /// If "t" is a non-null reference type "T" or a possibly-null type "T?"
  /// and "u" is a non-null reference type "U" or a possibly-null type "U?", then
  /// SameHead returns:
  ///            !allowNonNull     allowNonNull
  ///   T?  U?        true           true
  ///   T?  U         false          true
  ///   T   U?        false          false
  ///   T   U         true           true
  /// </summary>
  public static bool SameHead(Type t, Type u) {
    Contract.Requires(t != null);
    Contract.Requires(u != null);
    if (t is TypeProxy) {
      return t == u;
    } else if (t.TypeArgs.Count == 0) {
      return Equal_Improved(t, u);
    } else if (t is SetType) {
      return u is SetType && t.IsISetType == u.IsISetType;
    } else if (t is SeqType) {
      return u is SeqType;
    } else if (t is MultiSetType) {
      return u is MultiSetType;
    } else if (t is MapType) {
      return u is MapType && t.IsIMapType == u.IsIMapType;
    } else {
      var udtT = (UserDefinedType)t;
      var udtU = u as UserDefinedType;
      return udtU != null && udtT.ResolvedClass == udtU.ResolvedClass;
    }
  }

  /// <summary>
  /// Returns "true" iff the head symbols of "sub" can be a subtype of the head symbol of "super".
  /// Expects that neither "super" nor "sub" is an unresolved proxy type (but their type arguments are
  /// allowed to be, since this method does not inspect the type arguments).
  /// </summary>
  public static bool IsHeadSupertypeOf(Type super, Type sub) {
    Contract.Requires(super != null);
    Contract.Requires(sub != null);
    super = super.NormalizeExpandKeepConstraints();  // expand type synonyms
    var origSub = sub;
    sub = sub.NormalizeExpand();  // expand type synonyms AND constraints
    if (super is TypeProxy) {
      return super == sub;
    } else if (super is BoolType) {
      return sub is BoolType;
    } else if (super is CharType) {
      return sub is CharType;
    } else if (super is IntType) {
      return sub is IntType;
    } else if (super is RealType) {
      return sub is RealType;
    } else if (super is BitvectorType) {
      var bitvectorSuper = (BitvectorType)super;
      var bitvectorSub = sub as BitvectorType;
      return bitvectorSub != null && bitvectorSuper.Width == bitvectorSub.Width;
    } else if (super is IntVarietiesSupertype) {
      while (sub.AsNewtype != null) {
        sub = sub.AsNewtype.BaseType.NormalizeExpand();
      }
      return sub.IsIntegerType || sub is BitvectorType || sub is BigOrdinalType;
    } else if (super is RealVarietiesSupertype) {
      while (sub.AsNewtype != null) {
        sub = sub.AsNewtype.BaseType.NormalizeExpand();
      }
      return sub is RealType;
    } else if (super is BigOrdinalType) {
      return sub is BigOrdinalType;
    } else if (super is SetType) {
      return sub is SetType && (super.IsISetType || !sub.IsISetType);
    } else if (super is SeqType) {
      return sub is SeqType;
    } else if (super is MultiSetType) {
      return sub is MultiSetType;
    } else if (super is MapType) {
      return sub is MapType && (super.IsIMapType || !sub.IsIMapType);
    } else if (super is ArrowType) {
      var asuper = (ArrowType)super;
      var asub = sub as ArrowType;
      return asub != null && asuper.Arity == asub.Arity;
    } else if (super.IsObjectQ) {
      return sub.IsObjectQ || (sub is UserDefinedType { ResolvedClass: ClassLikeDecl cl } && cl.IsReferenceTypeDecl);
    } else if (super is UserDefinedType) {
      var udtSuper = (UserDefinedType)super;
      Contract.Assert(udtSuper.ResolvedClass != null);
      if (udtSuper.ResolvedClass is TypeParameter) {
        return udtSuper.ResolvedClass == sub.AsTypeParameter;
      } else {
        sub = origSub;  // get back to the starting point
        while (true) {
          sub = sub.NormalizeExpandKeepConstraints();  // skip past proxies and type synonyms
          var udtSub = sub as UserDefinedType;
          if (udtSub == null) {
            return false;
          } else if (udtSuper.ResolvedClass == udtSub.ResolvedClass) {
            return true;
          } else if (udtSub.ResolvedClass is SubsetTypeDecl) {
            sub = ((SubsetTypeDecl)udtSub.ResolvedClass).RhsWithArgument(udtSub.TypeArgs);
            if (udtSub.ResolvedClass is NonNullTypeDecl && udtSuper.ResolvedClass is NonNullTypeDecl) {
              // move "super" up the base-type chain, as was done with "sub", because non-nullness is essentially a co-variant type constructor
              var possiblyNullSuper = ((SubsetTypeDecl)udtSuper.ResolvedClass).RhsWithArgument(udtSuper.TypeArgs);
              udtSuper = (UserDefinedType)possiblyNullSuper;  // applying .RhsWithArgument to a NonNullTypeDecl should always yield a UserDefinedType
              if (udtSuper.IsObjectQ) {
                return true;
              }
            }
          } else if (udtSub.ResolvedClass is ClassLikeDecl) {
            var cl = (TopLevelDeclWithMembers)udtSub.ResolvedClass;
            return cl.HeadDerivesFrom(udtSuper.ResolvedClass);
          } else {
            return false;
          }
        }
      }
    } else {
      Contract.Assert(false);  // unexpected kind of type
      return true;  // to please the compiler
    }
  }

  /// <summary>
  /// Returns "true" iff "a" and "b" denote the same type, expanding type synonyms (but treating types with
  /// constraints as being separate types).
  /// Any unresolved proxy type contained in either "a" or "b" is compared with reference equality; in other
  /// words, the proxy itself is compared, not what the proxy will eventually stand for.
  /// </summary>
  public static bool Equal_Improved(Type a, Type b) {
    Contract.Requires(a != null);
    Contract.Requires(b != null);
    a = a.NormalizeExpandKeepConstraints();  // expand type synonyms
    b = b.NormalizeExpandKeepConstraints();  // expand type synonyms
    if (object.ReferenceEquals(a, b)) {
      return true;
    } else if (a is BoolType) {
      return b is BoolType;
    } else if (a is CharType) {
      return b is CharType;
    } else if (a is IntType) {
      return b is IntType;
    } else if (a is RealType) {
      return b is RealType;
    } else if (a is FieldType) {
      return b is FieldType;
    } else if (a is BitvectorType) {
      var bitvectorSuper = (BitvectorType)a;
      var bitvectorSub = b as BitvectorType;
      return bitvectorSub != null && bitvectorSuper.Width == bitvectorSub.Width;
    } else if (a is BigOrdinalType) {
      return b is BigOrdinalType;
    } else if (a is SetType) {
      return b is SetType && Equal_Improved(a.TypeArgs[0], b.TypeArgs[0]) && (a.IsISetType == b.IsISetType);
    } else if (a is SeqType) {
      return b is SeqType && Equal_Improved(a.TypeArgs[0], b.TypeArgs[0]);
    } else if (a is MultiSetType) {
      return b is MultiSetType && Equal_Improved(a.TypeArgs[0], b.TypeArgs[0]);
    } else if (a is MapType) {
      return b is MapType && Equal_Improved(a.TypeArgs[0], b.TypeArgs[0]) && Equal_Improved(a.TypeArgs[1], b.TypeArgs[1]) && (a.IsIMapType == b.IsIMapType);
    } else if (a is ArrowType) {
      var asuper = (ArrowType)a;
      var asub = b as ArrowType;
      return asub != null && asuper.Arity == asub.Arity;
    } else if (a is UserDefinedType) {
      var udtA = (UserDefinedType)a;
      Contract.Assert(udtA.ResolvedClass != null);
      if (udtA.ResolvedClass is TypeParameter) {
        Contract.Assert(udtA.TypeArgs.Count == 0);
        return udtA.ResolvedClass == b.AsTypeParameter;
      } else {
        var udtB = b as UserDefinedType;
        if (udtB == null) {
          return false;
        } else if (udtA.ResolvedClass != udtB.ResolvedClass) {
          return false;
        } else {
          Contract.Assert(udtA.TypeArgs.Count == udtB.TypeArgs.Count);
          for (int i = 0; i < udtA.TypeArgs.Count; i++) {
            if (!Equal_Improved(udtA.TypeArgs[i], udtB.TypeArgs[i])) {
              return false;
            }
          }
          return true;
        }
      }
    } else if (a is ResolverIdentifierExpr.ResolverTypeModule) {
      return b is ResolverIdentifierExpr.ResolverTypeModule;
    } else if (a is ResolverIdentifierExpr.ResolverTypeType) {
      return b is ResolverIdentifierExpr.ResolverTypeType;
    } else {
      // this is an unexpected type; however, it may be that we get here during the resolution of an erroneous
      // program, so we'll just return false
      return false;
    }
  }

  public static Type HeadWithProxyArgs(Type t) {
    Contract.Requires(t != null);
    Contract.Requires(!(t is TypeProxy));
    if (t.TypeArgs.Count == 0) {
      return t;
    } else if (t is SetType) {
      var s = (SetType)t;
      return new SetType(s.Finite, new InferredTypeProxy());
    } else if (t is MultiSetType) {
      return new MultiSetType(new InferredTypeProxy());
    } else if (t is SeqType) {
      return new SeqType(new InferredTypeProxy());
    } else if (t is MapType) {
      var s = (MapType)t;
      return new MapType(s.Finite, new InferredTypeProxy(), new InferredTypeProxy());
    } else if (t is ArrowType) {
      var s = (ArrowType)t;
      var args = s.TypeArgs.ConvertAll(_ => (Type)new InferredTypeProxy());
      return new ArrowType(s.Origin, (ArrowTypeDecl)s.ResolvedClass, args);
    } else {
      var s = (UserDefinedType)t;
      var args = s.TypeArgs.ConvertAll(_ => (Type)new InferredTypeProxy());
      return new UserDefinedType(s.Origin, s.Name, s.ResolvedClass, args);
    }
  }

  /// <summary>
  /// Returns a stack of base types leading to "type".  More precisely:
  ///
  /// With "typeSynonymsAreSignificant" being "false", then, of the tower returned,
  ///     tower[0] == type.NormalizeExpand()
  ///     tower.Last == type.NormalizeExpandKeepConstraints()
  /// In between, for consecutive indices i and i+1:
  ///     tower[i] is the base type (that is, .Rhs) of the subset type tower[i+1]
  /// The tower thus has the property that:
  ///     tower[0] is not a UserDefinedType with .ResolvedClass being a SubsetTypeDecl,
  ///     but all other tower[i] (for i > 0) are.
  ///
  /// With "typeSynonymsAreSignificant" being "true", then, of the tower returned,
  ///     tower[0] == type.Normalize()
  ///     tower.Last == type.NormalizeExpandKeepConstraints()
  /// In between, for consecutive indices i and i+1:
  ///     tower[i] is the base type (that is, .Rhs) of the subset type or type synonym tower[i+1]
  /// The tower thus has the property that:
  ///     tower[0] is not a UserDefinedType with .ResolvedClass being a TypeSynonymDecl,
  ///     but all other tower[i] (for i > 0) are.
  /// </summary>
  public static List<Type> GetTowerOfSubsetTypes(Type type, bool typeSynonymsAreSignificant = false) {
    Contract.Requires(type != null);
    type = typeSynonymsAreSignificant ? type.NormalizeAndAdjustForScope() : type.NormalizeExpandKeepConstraints();
    List<Type> tower;
    if (type is UserDefinedType { ResolvedClass: TypeSynonymDecl sst } && (typeSynonymsAreSignificant || sst is SubsetTypeDecl)) {
      var parent = sst.RhsWithArgument(type.TypeArgs);
      tower = GetTowerOfSubsetTypes(parent, typeSynonymsAreSignificant);
    } else {
      tower = [];
    }
    tower.Add(type);
    return tower;
  }

  /// <summary>
  /// For each i, computes some combination of a[i] and b[i], according to direction[i].
  /// For a negative direction (Contra), computes Join(a[i], b[i]), provided this join exists.
  /// For a zero direction (Inv), uses a[i], provided a[i] and b[i] are equal.
  /// For a positive direction (Co), computes Meet(a[i], b[i]), provided this meet exists.
  /// Returns null if any operation fails.
  /// </summary>
  public static List<Type> ComputeExtrema(List<TypeParameter.TPVariance> directions, List<Type> a, List<Type> b, SystemModuleManager systemModuleManager) {
    Contract.Requires(directions != null);
    Contract.Requires(a != null);
    Contract.Requires(b != null);
    Contract.Requires(directions.Count == a.Count);
    Contract.Requires(directions.Count == b.Count);
    Contract.Requires(systemModuleManager != null);
    var n = directions.Count;
    var r = new List<Type>(n);
    for (int i = 0; i < n; i++) {
      if (a[i].Normalize() is TypeProxy) {
        r.Add(b[i]);
      } else if (b[i].Normalize() is TypeProxy) {
        r.Add(a[i]);
      } else if (directions[i] == TypeParameter.TPVariance.Non) {
        if (a[i].Equals(b[i])) {
          r.Add(a[i]);
        } else {
          return null;
        }
      } else {
        var t = directions[i] == TypeParameter.TPVariance.Contra ? Join(a[i], b[i], systemModuleManager) : Meet(a[i], b[i], systemModuleManager);
        if (t == null) {
          return null;
        }
        r.Add(t);
      }
    }
    return r;
  }

  /// <summary>
  /// Does a best-effort to compute the join of "a" and "b", returning "null" if not successful.
  ///
  /// Since some type parameters may still be proxies, it could be that the returned type is not
  /// really a join, so the caller should set up additional constraints that the result is
  /// assignable to both a and b.
  /// </summary>
  public static Type Join(Type a, Type b, SystemModuleManager systemModuleManager) {
    Contract.Requires(a != null);
    Contract.Requires(b != null);
    Contract.Requires(systemModuleManager != null);
    var j = JoinX(a, b, systemModuleManager);
    if (systemModuleManager.Options.Get(CommonOptionBag.TypeInferenceDebug)) {
      systemModuleManager.Options.OutputWriter.Debug($"Join( {a}, {b} ) = {j}");
    }
    return j;
  }
  public static Type JoinX(Type a, Type b, SystemModuleManager systemModuleManager) {
    Contract.Requires(a != null);
    Contract.Requires(b != null);
    Contract.Requires(systemModuleManager != null);

    // As a special-case optimization, check for equality here, which will better preserve un-expanded type synonyms
    if (a.Equals(b, true)) {
      return a;
    }

    // Before we do anything else, make a note of whether or not both "a" and "b" are non-null types.
    var abNonNullTypes = a.IsNonNullRefType && b.IsNonNullRefType;

    var towerA = GetTowerOfSubsetTypes(a);
    var towerB = GetTowerOfSubsetTypes(b);
    for (var n = Math.Min(towerA.Count, towerB.Count); 1 <= --n;) {
      a = towerA[n];
      b = towerB[n];
      var udtA = (UserDefinedType)a;
      var udtB = (UserDefinedType)b;
      if (udtA.ResolvedClass == udtB.ResolvedClass) {
        // We have two subset types with equal heads
        if (a.Equals(b)) {  // optimization for a special case, which applies for example when there are no arguments or when the types happen to be the same
          return a;
        }
        Contract.Assert(a.TypeArgs.Count == b.TypeArgs.Count);
        var directions = udtA.ResolvedClass.TypeArgs.ConvertAll(tp => TypeParameter.Negate(tp.Variance));
        var typeArgs = ComputeExtrema(directions, a.TypeArgs, b.TypeArgs, systemModuleManager);
        if (typeArgs == null) {
          return null;
        }
        return new UserDefinedType(udtA.Origin, udtA.Name, udtA.ResolvedClass, typeArgs);
      }
    }
    // We exhausted all possibilities of subset types being equal, so use the base-most types.
    a = towerA[0];
    b = towerB[0];

    if (a is IntVarietiesSupertype) {
      return b is IntVarietiesSupertype || b.IsNumericBased(NumericPersuasion.Int) || b.IsBigOrdinalType || b.IsBitVectorType ? b : null;
    } else if (b is IntVarietiesSupertype) {
      return a.IsNumericBased(NumericPersuasion.Int) || a.IsBigOrdinalType || a.IsBitVectorType ? a : null;
    } else if (a.IsBoolType || a.IsCharType || a.IsBitVectorType || a.IsBigOrdinalType || a.IsTypeParameter || a.IsInternalTypeSynonym || a is TypeProxy) {
      return a.Equals(b) ? a : null;
    } else if (a is RealVarietiesSupertype) {
      return b is RealVarietiesSupertype || b.IsNumericBased(NumericPersuasion.Real) ? b : null;
    } else if (b is RealVarietiesSupertype) {
      return a.IsNumericBased(NumericPersuasion.Real) ? a : null;
    } else if (a.IsNumericBased()) {
      // Note, for join, we choose not to step down to IntVarietiesSupertype or RealVarietiesSupertype
      return a.Equals(b) ? a : null;
    } else if (a.IsBitVectorType) {
      return a.Equals(b) ? a : null;
    } else if (a is SetType) {
      var aa = (SetType)a;
      var bb = b as SetType;
      if (bb == null || aa.Finite != bb.Finite) {
        return null;
      }
      // sets are co-variant in their argument type
      var typeArg = Join(a.TypeArgs[0], b.TypeArgs[0], systemModuleManager);
      return typeArg == null ? null : new SetType(aa.Finite, typeArg);
    } else if (a is MultiSetType) {
      var aa = (MultiSetType)a;
      var bb = b as MultiSetType;
      if (bb == null) {
        return null;
      }
      // multisets are co-variant in their argument type
      var typeArg = Join(a.TypeArgs[0], b.TypeArgs[0], systemModuleManager);
      return typeArg == null ? null : new MultiSetType(typeArg);
    } else if (a is SeqType) {
      var aa = (SeqType)a;
      var bb = b as SeqType;
      if (bb == null) {
        return null;
      }
      // sequences are co-variant in their argument type
      var typeArg = Join(a.TypeArgs[0], b.TypeArgs[0], systemModuleManager);
      return typeArg == null ? null : new SeqType(typeArg);
    } else if (a is MapType) {
      var aa = (MapType)a;
      var bb = b as MapType;
      if (bb == null || aa.Finite != bb.Finite) {
        return null;
      }
      // maps are co-variant in both argument types
      var typeArgDomain = Join(a.TypeArgs[0], b.TypeArgs[0], systemModuleManager);
      var typeArgRange = Join(a.TypeArgs[1], b.TypeArgs[1], systemModuleManager);
      return typeArgDomain == null || typeArgRange == null ? null : new MapType(aa.Finite, typeArgDomain, typeArgRange);
    } else if (a.IsDatatype) {
      var aa = a.AsDatatype;
      if (aa != b.AsDatatype) {
        return null;
      }
      if (a.Equals(b)) {  // optimization for a special case, which applies for example when there are no arguments or when the types happen to be the same
        return a;
      }
      Contract.Assert(a.TypeArgs.Count == b.TypeArgs.Count);
      var directions = aa.TypeArgs.ConvertAll(tp => TypeParameter.Negate(tp.Variance));
      var typeArgs = ComputeExtrema(directions, a.TypeArgs, b.TypeArgs, systemModuleManager);
      if (typeArgs == null) {
        return null;
      }
      var udt = (UserDefinedType)a;
      return new UserDefinedType(udt.Origin, udt.Name, aa, typeArgs);
    } else if (a.AsArrowType != null) {
      var aa = a.AsArrowType;
      var bb = b.AsArrowType;
      if (bb == null || aa.Arity != bb.Arity) {
        return null;
      }
      int arity = aa.Arity;
      Contract.Assert(a.TypeArgs.Count == arity + 1);
      Contract.Assert(b.TypeArgs.Count == arity + 1);
      Contract.Assert(((ArrowType)a).ResolvedClass == ((ArrowType)b).ResolvedClass);
      var directions = new List<TypeParameter.TPVariance>();
      for (int i = 0; i < arity; i++) {
        directions.Add(TypeParameter.Negate(TypeParameter.TPVariance.Contra));  // arrow types are contra-variant in the argument types, so compute joins of these
      }
      directions.Add(TypeParameter.Negate(TypeParameter.TPVariance.Co));  // arrow types are co-variant in the result type, so compute the meet of these
      var typeArgs = ComputeExtrema(directions, a.TypeArgs, b.TypeArgs, systemModuleManager);
      if (typeArgs == null) {
        return null;
      }
      var arr = (ArrowType)aa;
      return new ArrowType(arr.Origin, (ArrowTypeDecl)arr.ResolvedClass, typeArgs);
    } else if (b.IsObjectQ) {
      var udtB = (UserDefinedType)b;
      return !a.IsRefType ? null : abNonNullTypes ? UserDefinedType.CreateNonNullType(udtB) : udtB;
    } else if (a.IsObjectQ) {
      var udtA = (UserDefinedType)a;
      return !b.IsRefType ? null : abNonNullTypes ? UserDefinedType.CreateNonNullType(udtA) : udtA;
    } else {
      // "a" is a class, trait, or abstract type
      var aa = ((UserDefinedType)a).ResolvedClass;
      Contract.Assert(aa != null);
      if (!(b is UserDefinedType)) {
        return null;
      }
      var bb = ((UserDefinedType)b).ResolvedClass;
      if (a.Equals(b)) {  // optimization for a special case, which applies for example when there are no arguments or when the types happen to be the same
        return a;
      } else if (aa == bb) {
        Contract.Assert(a.TypeArgs.Count == b.TypeArgs.Count);
        var directions = aa.TypeArgs.ConvertAll(tp => TypeParameter.Negate(tp.Variance));
        var typeArgs = ComputeExtrema(directions, a.TypeArgs, b.TypeArgs, systemModuleManager);
        if (typeArgs == null) {
          return null;
        }
        var udt = (UserDefinedType)a;
        var xx = new UserDefinedType(udt.Origin, udt.Name, aa, typeArgs);
        return abNonNullTypes ? UserDefinedType.CreateNonNullType(xx) : xx;
      } else if (aa is ClassLikeDecl && bb is ClassLikeDecl) {
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
      } else {
        return null;
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
  public static Type Meet(Type a, Type b, SystemModuleManager systemModuleManager) {
    Contract.Requires(a != null);
    Contract.Requires(b != null);
    Contract.Requires(systemModuleManager != null);
    a = a.NormalizeExpandKeepConstraints();
    b = b.NormalizeExpandKeepConstraints();

    var joinNeedsNonNullConstraint = false;
    Type j;
    if (a is UserDefinedType { ResolvedClass: NonNullTypeDecl aClass }) {
      joinNeedsNonNullConstraint = true;
      j = MeetX(aClass.RhsWithArgument(a.TypeArgs), b, systemModuleManager);
    } else if (b is UserDefinedType { ResolvedClass: NonNullTypeDecl bClass }) {
      joinNeedsNonNullConstraint = true;
      j = MeetX(a, bClass.RhsWithArgument(b.TypeArgs), systemModuleManager);
    } else {
      j = MeetX(a, b, systemModuleManager);
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
      systemModuleManager.Options.OutputWriter.Debug($"Meet( {a}, {b} ) = {j}");
    }
    return j;
  }
  public static Type MeetX(Type a, Type b, SystemModuleManager systemModuleManager) {
    Contract.Requires(a != null);
    Contract.Requires(b != null);
    Contract.Requires(systemModuleManager != null);

    a = a.NormalizeExpandKeepConstraints();
    b = b.NormalizeExpandKeepConstraints();
    if (a is IntVarietiesSupertype) {
      return b is IntVarietiesSupertype || b.IsNumericBased(NumericPersuasion.Int) || b.IsBigOrdinalType || b.IsBitVectorType ? b : null;
    } else if (b is IntVarietiesSupertype) {
      return a.IsNumericBased(NumericPersuasion.Int) || a.IsBigOrdinalType || a.IsBitVectorType ? a : null;
    } else if (a is RealVarietiesSupertype) {
      return b is RealVarietiesSupertype || b.IsNumericBased(NumericPersuasion.Real) ? b : null;
    } else if (b is RealVarietiesSupertype) {
      return a.IsNumericBased(NumericPersuasion.Real) ? a : null;
    }

    var towerA = GetTowerOfSubsetTypes(a);
    var towerB = GetTowerOfSubsetTypes(b);
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
        if (a.Equals(b)) {  // optimization for a special case, which applies for example when there are no arguments or when the types happen to be the same
          return a;
        }
        Contract.Assert(a.TypeArgs.Count == b.TypeArgs.Count);
        var directions = udtA.ResolvedClass.TypeArgs.ConvertAll(tp => tp.Variance);
        var typeArgs = ComputeExtrema(directions, a.TypeArgs, b.TypeArgs, systemModuleManager);
        if (typeArgs == null) {
          return null;
        }
        return new UserDefinedType(udtA.Origin, udtA.Name, udtA.ResolvedClass, typeArgs);
      } else {
        // The two subset types do not have the same head, so there is no meet
        return null;
      }
    }
    Contract.Assert(towerA.Count == 1 && towerB.Count == 1);

    if (a.IsBoolType || a.IsCharType || a.IsNumericBased() || a.IsBitVectorType || a.IsBigOrdinalType || a.IsTypeParameter || a.IsInternalTypeSynonym || a is TypeProxy) {
      return a.Equals(b) ? a : null;
    } else if (a is SetType) {
      var aa = (SetType)a;
      var bb = b as SetType;
      if (bb == null || aa.Finite != bb.Finite) {
        return null;
      }
      // sets are co-variant in their argument type
      var typeArg = Meet(a.TypeArgs[0], b.TypeArgs[0], systemModuleManager);
      return typeArg == null ? null : new SetType(aa.Finite, typeArg);
    } else if (a is MultiSetType) {
      var aa = (MultiSetType)a;
      var bb = b as MultiSetType;
      if (bb == null) {
        return null;
      }
      // multisets are co-variant in their argument type
      var typeArg = Meet(a.TypeArgs[0], b.TypeArgs[0], systemModuleManager);
      return typeArg == null ? null : new MultiSetType(typeArg);
    } else if (a is SeqType) {
      var aa = (SeqType)a;
      var bb = b as SeqType;
      if (bb == null) {
        return null;
      }
      // sequences are co-variant in their argument type
      var typeArg = Meet(a.TypeArgs[0], b.TypeArgs[0], systemModuleManager);
      return typeArg == null ? null : new SeqType(typeArg);
    } else if (a is MapType) {
      var aa = (MapType)a;
      var bb = b as MapType;
      if (bb == null || aa.Finite != bb.Finite) {
        return null;
      }
      // maps are co-variant in both argument types
      var typeArgDomain = Meet(a.TypeArgs[0], b.TypeArgs[0], systemModuleManager);
      var typeArgRange = Meet(a.TypeArgs[1], b.TypeArgs[1], systemModuleManager);
      return typeArgDomain == null || typeArgRange == null ? null : new MapType(aa.Finite, typeArgDomain, typeArgRange);
    } else if (a.IsDatatype) {
      var aa = a.AsDatatype;
      if (aa != b.AsDatatype) {
        return null;
      }
      if (a.Equals(b)) {  // optimization for a special case, which applies for example when there are no arguments or when the types happen to be the same
        return a;
      }
      Contract.Assert(a.TypeArgs.Count == b.TypeArgs.Count);
      var directions = aa.TypeArgs.ConvertAll(tp => tp.Variance);
      var typeArgs = ComputeExtrema(directions, a.TypeArgs, b.TypeArgs, systemModuleManager);
      if (typeArgs == null) {
        return null;
      }
      var udt = (UserDefinedType)a;
      return new UserDefinedType(udt.Origin, udt.Name, aa, typeArgs);
    } else if (a.AsArrowType != null) {
      var aa = a.AsArrowType;
      var bb = b.AsArrowType;
      if (bb == null || aa.Arity != bb.Arity) {
        return null;
      }
      int arity = aa.Arity;
      Contract.Assert(a.TypeArgs.Count == arity + 1);
      Contract.Assert(b.TypeArgs.Count == arity + 1);
      Contract.Assert(((ArrowType)a).ResolvedClass == ((ArrowType)b).ResolvedClass);
      var directions = new List<TypeParameter.TPVariance>();
      for (int i = 0; i < arity; i++) {
        directions.Add(TypeParameter.TPVariance.Contra);  // arrow types are contra-variant in the argument types, so compute joins of these
      }
      directions.Add(TypeParameter.TPVariance.Co);  // arrow types are co-variant in the result type, so compute the meet of these
      var typeArgs = ComputeExtrema(directions, a.TypeArgs, b.TypeArgs, systemModuleManager);
      if (typeArgs == null) {
        return null;
      }
      var arr = (ArrowType)aa;
      return new ArrowType(arr.Origin, (ArrowTypeDecl)arr.ResolvedClass, typeArgs);
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
      if (a.Equals(b)) {  // optimization for a special case, which applies for example when there are no arguments or when the types happen to be the same
        return a;
      } else if (aa == bb) {
        Contract.Assert(a.TypeArgs.Count == b.TypeArgs.Count);
        var directions = aa.TypeArgs.ConvertAll(tp => tp.Variance);
        var typeArgs = ComputeExtrema(directions, a.TypeArgs, b.TypeArgs, systemModuleManager);
        if (typeArgs == null) {
          return null;
        }
        var udt = (UserDefinedType)a;
        return new UserDefinedType(udt.Origin, udt.Name, aa, typeArgs);
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

  public void ForeachTypeComponent(Action<Type> action) {
    action(this);
    TypeArgs.ForEach(x => x.ForeachTypeComponent(action));
  }

  public bool ContainsProxy(TypeProxy proxy) {
    Contract.Requires(proxy != null && proxy.T == null);
    if (this == proxy) {
      return true;
    } else {
      return TypeArgs.Exists(t => t.ContainsProxy(proxy));
    }
  }

  public virtual List<Type> ParentTypes(bool includeTypeBounds) {
    return [];
  }

  /// <summary>
  /// Return whether or not "this" is a subtype of "super".
  /// If "ignoreTypeArguments" is "true", then proceed as if the type arguments were equal.
  /// If "ignoreNullity" is "true", then the difference between a non-null reference type C
  /// and the corresponding nullable reference type C? is ignored.
  /// </summary>
  public virtual bool IsSubtypeOf(Type super, bool ignoreTypeArguments, bool ignoreNullity) {
    Contract.Requires(super != null);

    super = super.NormalizeExpandKeepConstraints();
    var sub = NormalizeExpandKeepConstraints();
    bool equivalentHeads = SameHead(sub, super);
    if (!equivalentHeads && ignoreNullity) {
      if (super is UserDefinedType a && sub is UserDefinedType b) {
        var clA = (a.ResolvedClass as NonNullTypeDecl)?.Class ?? a.ResolvedClass;
        var clB = (b.ResolvedClass as NonNullTypeDecl)?.Class ?? b.ResolvedClass;
        equivalentHeads = clA == clB;
      }
    }
    if (equivalentHeads) {
      return ignoreTypeArguments || CompatibleTypeArgs(super, sub);
    }

    // There is a special case, namely when super is the non-null "object". Since "sub.ParentTypes()" only gives
    // back the explicitly declared parent traits, the general case below may miss it.
    if (super.IsObject) {
      return sub.IsNonNullRefType;
    }

    return sub.ParentTypes(true).Any(parentType => parentType.IsSubtypeOf(super, ignoreTypeArguments, ignoreNullity));
  }

  public static bool CompatibleTypeArgs(Type super, Type sub) {
    var polarities = GetPolarities(super);
    Contract.Assert(polarities.Count == super.TypeArgs.Count && polarities.Count == sub.TypeArgs.Count);
    var allGood = true;
    for (int i = 0; allGood && i < polarities.Count; i++) {
      switch (polarities[i]) {
        case TypeParameter.TPVariance.Co:
          allGood = IsSupertype(super.TypeArgs[i], sub.TypeArgs[i]);
          break;
        case TypeParameter.TPVariance.Contra:
          allGood = IsSupertype(sub.TypeArgs[i], super.TypeArgs[i]);
          break;
        case TypeParameter.TPVariance.Non:
        default:  // "default" shouldn't ever happen
          allGood = Equal_Improved(super.TypeArgs[i], sub.TypeArgs[i]);
          break;
      }
    }
    return allGood;
  }
}

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

  [SyntaxConstructor]
  public CharType(IOrigin origin) : base(origin) { }

  public CharType() { }

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
  [SyntaxConstructor]
  public RealType(IOrigin origin) : base(origin) {
  }

  public RealType() {
  }
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
  [SyntaxConstructor]
  public BigOrdinalType(IOrigin origin) : base(origin) {
  }

  public BigOrdinalType() {
  }

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
  public int Width;
  public NativeType NativeType;

  [SyntaxConstructor]
  public BitvectorType(IOrigin origin, int width) : base(origin) {
    Contract.Requires(0 <= width);
    Width = width;
  }

  public BitvectorType() {
  }

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
      Contract.Assert(false); throw new Cce.UnreachableException();
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

public class FieldType : BasicType {
  [SyntaxConstructor]
  public FieldType(IOrigin origin) : base(origin) {
  }

  public FieldType() {
  }
  [System.Diagnostics.Contracts.Pure]
  public override string TypeName(DafnyOptions options, ModuleDefinition context, bool parseAble) {
    return "field";
  }
  public override bool Equals(Type that, bool keepConstraints = false) {
    return that.NormalizeExpand(keepConstraints) is FieldType;
  }
  public override bool IsSubtypeOf(Type super, bool ignoreTypeArguments, bool ignoreNullity) {
    if (super is FieldType) {
      return true;
    }
    return base.IsSubtypeOf(super, ignoreTypeArguments, ignoreNullity);
  }
}

public abstract class TypeProxy : Type {
  public override IEnumerable<INode> Children => Enumerable.Empty<Node>();
  [FilledInDuringResolution] public Type T;
  public List<TypeConstraint> SupertypeConstraints = [];
  public List<TypeConstraint> SubtypeConstraints = [];

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

  internal TypeProxy(IOrigin origin = null) : base() {
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
  /// Whether the typeProxy should be inferred to base type or as subset type
  public bool KeepConstraints = false;

  public InferredTypeProxy(IOrigin origin = null) : base(origin) {
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
