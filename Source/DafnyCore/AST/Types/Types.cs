#define TI_DEBUG_PRINT
using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Threading;

namespace Microsoft.Dafny;

public abstract class Type : INode {
  public static readonly BoolType Bool = new BoolType();
  public static readonly CharType Char = new CharType();
  public static readonly IntType Int = new IntType();
  public static readonly RealType Real = new RealType();
  public override IEnumerable<INode> Children { get; } = new List<INode>();
  public static Type Nat() { return new UserDefinedType(Token.NoToken, "nat", null); }  // note, this returns an unresolved type
  public static Type String() { return new UserDefinedType(Token.NoToken, "string", null); }  // note, this returns an unresolved type
  public static readonly BigOrdinalType BigOrdinal = new BigOrdinalType();

  private static AsyncLocal<List<VisibilityScope>> _scopes = new();
  private static List<VisibilityScope> Scopes => _scopes.Value ??= new();

  [ThreadStatic]
  private static bool scopesEnabled = false;

  public virtual IEnumerable<INode> Nodes => Enumerable.Empty<INode>();

  public static void PushScope(VisibilityScope scope) {
    Scopes.Add(scope);
  }

  public static void ResetScopes() {
    _scopes.Value = new();
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

  public static string TypeArgsToString(ModuleDefinition/*?*/ context, List<Type> typeArgs, bool parseAble = false) {
    Contract.Requires(typeArgs == null ||
                      (typeArgs.All(ty => ty != null && ty.TypeName(context, parseAble) != null) &&
                       (typeArgs.All(ty => ty.TypeName(context, parseAble).StartsWith("_")) ||
                        typeArgs.All(ty => !ty.TypeName(context, parseAble).StartsWith("_")))));

    if (typeArgs != null && typeArgs.Count > 0 &&
        (!parseAble || !typeArgs[0].TypeName(context, parseAble).StartsWith("_"))) {
      return string.Format("<{0}>", Util.Comma(typeArgs, ty => ty.TypeName(context, parseAble)));
    }
    return "";
  }

  public static string TypeArgsToString(List<Type> typeArgs, bool parseAble = false) {
    return TypeArgsToString(null, typeArgs, parseAble);
  }

  public string TypeArgsToString(ModuleDefinition/*?*/ context, bool parseAble = false) {
    return Type.TypeArgsToString(context, this.TypeArgs, parseAble);
  }

  // Type arguments to the type
  public List<Type> TypeArgs = new List<Type>();

  /// <summary>
  /// Add to "tps" the free type parameters in "this".
  /// Requires the type to be resolved.
  /// </summary>
  public void AddFreeTypeParameters(ISet<TypeParameter> tps) {
    Contract.Requires(tps != null);
    var ty = this.NormalizeExpandKeepConstraints();
    var tp = ty.AsTypeParameter;
    if (tp != null) {
      tps.Add(tp);
    }
    foreach (var ta in ty.TypeArgs) {
      ta.AddFreeTypeParameters(tps);
    }
  }

  [Pure]
  public abstract string TypeName(ModuleDefinition/*?*/ context, bool parseAble = false);
  [Pure]
  public override string ToString() {
    return TypeName(null, false);
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
      var pt = type as TypeProxy;
      if (pt != null && pt.T != null) {
        type = pt.T;
      } else {
        return type;
      }
    }
  }

  /// <summary>
  /// Return the type that "this" stands for, getting to the bottom of proxies and following type synonyms.
  ///
  /// For more documentation, see method Normalize().
  /// </summary>
  [Pure]
  public Type NormalizeExpand(bool keepConstraints = false) {
    Contract.Ensures(Contract.Result<Type>() != null);
    Contract.Ensures(!(Contract.Result<Type>() is TypeProxy) || ((TypeProxy)Contract.Result<Type>()).T == null);  // return a proxy only if .T == null
    Type type = this;
    while (true) {

      var pt = type as TypeProxy;
      if (pt != null && pt.T != null) {
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
          if (rtd is ClassDecl cl) {
            Contract.Assert(cl.NonNullTypeDecl != null);
            Contract.Assert(cl.NonNullTypeDecl.IsVisibleInScope(scope));
          } else {
            Contract.Assert(rtd is OpaqueTypeDecl);
          }
        }

        if (rtd.IsRevealedInScope(scope)) {
          if (rtd is TypeSynonymDecl && (!(rtd is SubsetTypeDecl) || !keepConstraints)) {
            type = ((TypeSynonymDecl)rtd).RhsWithArgumentIgnoringScope(udt.TypeArgs);
            continue;
          } else {
            return type;
          }
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
          var cl = ((UserDefinedType)rhs).ResolvedClass as ClassDecl;
          Contract.Assert(cl != null && cl.NonNullTypeDecl != null);
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
  /// Return the type that "this" stands for, getting to the bottom of proxies and following type synonyms, but does
  /// not follow subset types.
  ///
  /// For more documentation, see method Normalize().
  /// </summary>
  [Pure]
  public Type NormalizeExpandKeepConstraints() {
    return NormalizeExpand(true);
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
        var cl = rtd as ClassDecl;
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
  [Pure]
  public abstract bool Equals(Type that, bool keepConstraints = false);

  public bool IsBoolType { get { return NormalizeExpand() is BoolType; } }
  public bool IsCharType { get { return NormalizeExpand() is CharType; } }
  public bool IsIntegerType { get { return NormalizeExpand() is IntType; } }
  public bool IsRealType { get { return NormalizeExpand() is RealType; } }
  public bool IsBigOrdinalType { get { return NormalizeExpand() is BigOrdinalType; } }
  public bool IsBitVectorType { get { return AsBitVectorType != null; } }
  public bool IsStringType { get { return AsSeqType?.Arg.IsCharType == true; } }
  public BitvectorType AsBitVectorType { get { return NormalizeExpand() as BitvectorType; } }
  public bool IsNumericBased() {
    var t = NormalizeExpand();
    return t.IsIntegerType || t.IsRealType || t.AsNewtype != null;
  }
  public enum NumericPersuasion { Int, Real }
  [Pure]
  public bool IsNumericBased(NumericPersuasion p) {
    Type t = this;
    while (true) {
      t = t.NormalizeExpand();
      if (t.IsIntegerType) {
        return p == NumericPersuasion.Int;
      } else if (t.IsRealType) {
        return p == NumericPersuasion.Real;
      }
      var d = t.AsNewtype;
      if (d == null) {
        return false;
      }
      t = d.BaseType;
    }
  }

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

    AutoInitInfo CharacteristicToAutoInitInfo(TypeParameter.TypeParameterCharacteristics c) {
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
    }

    var udt = (UserDefinedType)t;
    var cl = udt.ResolvedClass;
    Contract.Assert(cl != null);
    if (cl is OpaqueTypeDecl) {
      var otd = (OpaqueTypeDecl)cl;
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
          throw new cce.UnreachableException();
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
          throw new cce.UnreachableException();
      }
    } else if (cl is ClassDecl) {
      return AutoInitInfo.CompilableValue; // null is a value of this type
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
          coDatatypesBeingVisited = new List<UserDefinedType>(coDatatypesBeingVisited);
        } else {
          coDatatypesBeingVisited = new List<UserDefinedType>();
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
      throw new cce.UnreachableException();
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
      var udt = NormalizeExpand() as UserDefinedType;
      return udt != null && udt.ResolvedClass is ClassDecl && !(udt.ResolvedClass is ArrowTypeDecl);
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
      var udt = NormalizeExpandKeepConstraints() as UserDefinedType;
      return udt != null && udt.ResolvedClass is ClassDecl && ((ClassDecl)udt.ResolvedClass).IsObjectTrait;
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
        return nonNullRefDecl.Class.IsObjectTrait;
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
        var udt = t.NormalizeExpandKeepConstraints() as UserDefinedType;
        if (udt == null) {
          return null;
        }
        if (udt.ResolvedClass is NonNullTypeDecl) {
          return udt;
        }
        var sst = udt.ResolvedClass as SubsetTypeDecl;
        if (sst != null) {
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
      udt = isyn.RhsWithArgumentIgnoringScope(udt.TypeArgs) as UserDefinedType;
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
    return new UserDefinedType(udt.tok, parent.Name, parent, typeArgs);
  }
  public bool IsTraitType {
    get {
      return AsTraitType != null;
    }
  }
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
      var t = NormalizeExpand();
      var udt = UserDefinedType.DenotesClass(t);
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
  public bool IsArrowType {
    get { return AsArrowType != null; }
  }
  public ArrowType AsArrowType {
    get {
      var t = NormalizeExpand();
      return t as ArrowType;
    }
  }

  public bool IsMapType {
    get {
      var t = NormalizeExpand() as MapType;
      return t != null && t.Finite;
    }
  }
  public bool IsIMapType {
    get {
      var t = NormalizeExpand() as MapType;
      return t != null && !t.Finite;
    }
  }
  public bool IsISetType {
    get {
      var t = NormalizeExpand() as SetType;
      return t != null && !t.Finite;
    }
  }
  public NewtypeDecl AsNewtype {
    get {
      var udt = NormalizeExpand() as UserDefinedType;
      return udt == null ? null : udt.ResolvedClass as NewtypeDecl;
    }
  }
  public TypeSynonymDecl AsTypeSynonym {
    get {
      var udt = this as UserDefinedType;  // note, it is important to use 'this' here, not 'this.NormalizeExpand()'
      if (udt == null) {
        return null;
      } else {
        return udt.ResolvedClass as TypeSynonymDecl;
      }
    }
  }
  public InternalTypeSynonymDecl AsInternalTypeSynonym {
    get {
      var udt = this as UserDefinedType;  // note, it is important to use 'this' here, not 'this.NormalizeExpand()'
      if (udt == null) {
        return null;
      } else {
        return udt.ResolvedClass as InternalTypeSynonymDecl;
      }
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
      if (udt == null) {
        return null;
      } else {
        return (udt.ResolvedClass as RevealableTypeDecl);
      }
    }
  }
  public bool IsRevealableType {
    get { return AsRevealableType != null; }
  }
  public bool IsDatatype {
    get {
      return AsDatatype != null;
    }
  }
  public DatatypeDecl AsDatatype {
    get {
      var udt = NormalizeExpand() as UserDefinedType;
      if (udt == null) {
        return null;
      } else {
        return udt.ResolvedClass as DatatypeDecl;
      }
    }
  }
  public bool IsIndDatatype {
    get {
      return AsIndDatatype != null;
    }
  }
  public IndDatatypeDecl AsIndDatatype {
    get {
      var udt = NormalizeExpand() as UserDefinedType;
      if (udt == null) {
        return null;
      } else {
        return udt.ResolvedClass as IndDatatypeDecl;
      }
    }
  }
  public bool IsCoDatatype {
    get {
      return AsCoDatatype != null;
    }
  }
  public CoDatatypeDecl AsCoDatatype {
    get {
      var udt = NormalizeExpand() as UserDefinedType;
      if (udt == null) {
        return null;
      } else {
        return udt.ResolvedClass as CoDatatypeDecl;
      }
    }
  }
  public bool InvolvesCoDatatype {
    get {
      return IsCoDatatype;  // TODO: should really check structure of the type recursively
    }
  }
  public bool IsTypeParameter {
    get {
      return AsTypeParameter != null;
    }
  }
  public bool IsInternalTypeSynonym {
    get { return AsInternalTypeSynonym != null; }
  }
  public TypeParameter AsTypeParameter {
    get {
      var ct = NormalizeExpandKeepConstraints() as UserDefinedType;
      return ct?.ResolvedClass as TypeParameter;
    }
  }
  public bool IsOpaqueType {
    get { return AsOpaqueType != null; }
  }
  public OpaqueTypeDecl AsOpaqueType {
    get {
      var udt = this.Normalize() as UserDefinedType;  // note, it is important to use 'this.Normalize()' here, not 'this.NormalizeExpand()'
      return udt?.ResolvedClass as OpaqueTypeDecl;
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
      return !ct.IsTypeParameter && !ct.IsOpaqueType && !ct.IsInternalTypeSynonym && !ct.IsCoDatatype && !ct.IsArrowType && !ct.IsIMapType && !ct.IsISetType;
    }
  }

  /// <summary>
  /// Returns "true" if:  Given a value of type "this", can we determine at run time if the
  /// value is a member of type "target"?
  /// </summary>
  public bool IsTestableToBe(Type target) {
    Contract.Requires(target != null);

    // First up, we know how to check for null, so let's expand "target" and "source"
    // past any type synonyms and also past any (built-in) non-null constraint.
    var source = this.NormalizeExpandKeepConstraints();
    if (source is UserDefinedType && ((UserDefinedType)source).ResolvedClass is NonNullTypeDecl) {
      source = source.NormalizeExpand(); // also lop off non-null constraint
    }
    target = target.NormalizeExpandKeepConstraints();
    if (target is UserDefinedType && ((UserDefinedType)target).ResolvedClass is NonNullTypeDecl) {
      target = target.NormalizeExpand(); // also lop off non-null constraint
    }

    if (source.IsSubtypeOf(target, false, true)) {
      // Every value of "source" (except possibly "null") is also a member of type "target",
      // so no run-time test is needed (except possibly a null check).
      return true;
#if SOON  // include in a coming PR that sorts this one in the compilers
      } else if (target is UserDefinedType udt && (udt.ResolvedClass is SubsetTypeDecl || udt.ResolvedClass is NewtypeDecl)) {
        // The type of the bound variable has a constraint. Such a constraint is a ghost expression, so it cannot
        // (in general) by checked at run time. (A possible enhancement here would be to look at the type constraint
        // to if it is compilable after all.)
        var constraints = target.GetTypeConstraints();
        return false;
#endif
    } else if (target.TypeArgs.Count == 0) {
      // No type parameters. So, we just need to check the run-time class/interface type.
      return true;
    } else {
      // We give up.
      return false;
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
      return new List<TypeParameter.TPVariance>();
    } else if (type is MapType) {
      return new List<TypeParameter.TPVariance> { TypeParameter.TPVariance.Co, TypeParameter.TPVariance.Co };
    } else if (type is CollectionType) {
      return new List<TypeParameter.TPVariance> { TypeParameter.TPVariance.Co };
    } else {
      var udf = (UserDefinedType)type;
      if (udf.TypeArgs.Count == 0) {
        return new List<TypeParameter.TPVariance>();
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
      var tt = ((UserDefinedType)t).ResolvedClass as ClassDecl;
      var uu = ((UserDefinedType)u).ResolvedClass as ClassDecl;
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
      var clSub = sub as UserDefinedType;
      return sub.IsObjectQ || (clSub != null && clSub.ResolvedClass is ClassDecl);
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
          } else if (udtSub.ResolvedClass is ClassDecl) {
            var cl = (ClassDecl)udtSub.ResolvedClass;
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
  /// Expects that neither "a" nor "b" is or contains an unresolved proxy type.
  /// </summary>
  public static bool Equal_Improved(Type a, Type b) {
    Contract.Requires(a != null);
    Contract.Requires(b != null);
    a = a.NormalizeExpandKeepConstraints();  // expand type synonyms
    b = b.NormalizeExpandKeepConstraints();  // expand type synonyms
    if (a is BoolType) {
      return b is BoolType;
    } else if (a is CharType) {
      return b is CharType;
    } else if (a is IntType) {
      return b is IntType;
    } else if (a is RealType) {
      return b is RealType;
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
    } else if (a is Resolver_IdentifierExpr.ResolverType_Module) {
      return b is Resolver_IdentifierExpr.ResolverType_Module;
    } else if (a is Resolver_IdentifierExpr.ResolverType_Type) {
      return b is Resolver_IdentifierExpr.ResolverType_Type;
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
      return new ArrowType(s.tok, (ArrowTypeDecl)s.ResolvedClass, args);
    } else {
      var s = (UserDefinedType)t;
      var args = s.TypeArgs.ConvertAll(_ => (Type)new InferredTypeProxy());
      return new UserDefinedType(s.tok, s.Name, s.ResolvedClass, args);
    }
  }

  /// <summary>
  /// Returns a stack of base types leading to "type".  More precisely, of the tower returned,
  ///     tower[0] == type.NormalizeExpand()
  ///     tower.Last == type.NormalizeExpandKeepConstraints()
  /// In between, for consecutive indices i and i+1:
  ///     tower[i] is the base type (that is, .Rhs) of the subset type tower[i+1]
  /// The tower thus has the property that:
  ///     tower[0] is not a UserDefinedType with .ResolvedClass being a SubsetTypeDecl,
  ///     but all other tower[i] (for i > 0) are.
  /// </summary>
  public static List<Type> GetTowerOfSubsetTypes(Type type) {
    Contract.Requires(type != null);
    type = type.NormalizeExpandKeepConstraints();
    List<Type> tower;
    if (type is UserDefinedType { ResolvedClass: SubsetTypeDecl sst }) {
      var parent = sst.RhsWithArgument(type.TypeArgs);
      tower = GetTowerOfSubsetTypes(parent);
    } else {
      tower = new List<Type>();
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
  public static List<Type> ComputeExtrema(List<TypeParameter.TPVariance> directions, List<Type> a, List<Type> b, BuiltIns builtIns) {
    Contract.Requires(directions != null);
    Contract.Requires(a != null);
    Contract.Requires(b != null);
    Contract.Requires(directions.Count == a.Count);
    Contract.Requires(directions.Count == b.Count);
    Contract.Requires(builtIns != null);
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
        var t = directions[i] == TypeParameter.TPVariance.Contra ? Join(a[i], b[i], builtIns) : Meet(a[i], b[i], builtIns);
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
  public static Type Join(Type a, Type b, BuiltIns builtIns) {
    Contract.Requires(a != null);
    Contract.Requires(b != null);
    Contract.Requires(builtIns != null);
    var j = JoinX(a, b, builtIns);
    if (DafnyOptions.O.TypeInferenceDebug) {
      Console.WriteLine("DEBUG: Join( {0}, {1} ) = {2}", a, b, j);
    }
    return j;
  }
  public static Type JoinX(Type a, Type b, BuiltIns builtIns) {
    Contract.Requires(a != null);
    Contract.Requires(b != null);
    Contract.Requires(builtIns != null);

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
        var typeArgs = ComputeExtrema(directions, a.TypeArgs, b.TypeArgs, builtIns);
        if (typeArgs == null) {
          return null;
        }
        return new UserDefinedType(udtA.tok, udtA.Name, udtA.ResolvedClass, typeArgs);
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
      var typeArg = Join(a.TypeArgs[0], b.TypeArgs[0], builtIns);
      return typeArg == null ? null : new SetType(aa.Finite, typeArg);
    } else if (a is MultiSetType) {
      var aa = (MultiSetType)a;
      var bb = b as MultiSetType;
      if (bb == null) {
        return null;
      }
      // multisets are co-variant in their argument type
      var typeArg = Join(a.TypeArgs[0], b.TypeArgs[0], builtIns);
      return typeArg == null ? null : new MultiSetType(typeArg);
    } else if (a is SeqType) {
      var aa = (SeqType)a;
      var bb = b as SeqType;
      if (bb == null) {
        return null;
      }
      // sequences are co-variant in their argument type
      var typeArg = Join(a.TypeArgs[0], b.TypeArgs[0], builtIns);
      return typeArg == null ? null : new SeqType(typeArg);
    } else if (a is MapType) {
      var aa = (MapType)a;
      var bb = b as MapType;
      if (bb == null || aa.Finite != bb.Finite) {
        return null;
      }
      // maps are co-variant in both argument types
      var typeArgDomain = Join(a.TypeArgs[0], b.TypeArgs[0], builtIns);
      var typeArgRange = Join(a.TypeArgs[1], b.TypeArgs[1], builtIns);
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
      var typeArgs = ComputeExtrema(directions, a.TypeArgs, b.TypeArgs, builtIns);
      if (typeArgs == null) {
        return null;
      }
      var udt = (UserDefinedType)a;
      return new UserDefinedType(udt.tok, udt.Name, aa, typeArgs);
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
      var typeArgs = ComputeExtrema(directions, a.TypeArgs, b.TypeArgs, builtIns);
      if (typeArgs == null) {
        return null;
      }
      var arr = (ArrowType)aa;
      return new ArrowType(arr.tok, (ArrowTypeDecl)arr.ResolvedClass, typeArgs);
    } else if (b.IsObjectQ) {
      var udtB = (UserDefinedType)b;
      return !a.IsRefType ? null : abNonNullTypes ? UserDefinedType.CreateNonNullType(udtB) : udtB;
    } else if (a.IsObjectQ) {
      var udtA = (UserDefinedType)a;
      return !b.IsRefType ? null : abNonNullTypes ? UserDefinedType.CreateNonNullType(udtA) : udtA;
    } else {
      // "a" is a class, trait, or opaque type
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
        var typeArgs = ComputeExtrema(directions, a.TypeArgs, b.TypeArgs, builtIns);
        if (typeArgs == null) {
          return null;
        }
        var udt = (UserDefinedType)a;
        var xx = new UserDefinedType(udt.tok, udt.Name, aa, typeArgs);
        return abNonNullTypes ? UserDefinedType.CreateNonNullType(xx) : xx;
      } else if (aa is ClassDecl && bb is ClassDecl) {
        var A = (ClassDecl)aa;
        var B = (ClassDecl)bb;
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
          return abNonNullTypes ? UserDefinedType.CreateNonNullType(builtIns.ObjectQ()) : builtIns.ObjectQ();
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
  public static Type Meet(Type a, Type b, BuiltIns builtIns) {
    Contract.Requires(a != null);
    Contract.Requires(b != null);
    Contract.Requires(builtIns != null);
    a = a.NormalizeExpandKeepConstraints();
    b = b.NormalizeExpandKeepConstraints();

    var joinNeedsNonNullConstraint = false;
    Type j;
    if (a is UserDefinedType { ResolvedClass: NonNullTypeDecl aClass }) {
      joinNeedsNonNullConstraint = true;
      j = MeetX(aClass.RhsWithArgument(a.TypeArgs), b, builtIns);
    } else if (b is UserDefinedType { ResolvedClass: NonNullTypeDecl bClass }) {
      joinNeedsNonNullConstraint = true;
      j = MeetX(a, bClass.RhsWithArgument(b.TypeArgs), builtIns);
    } else {
      j = MeetX(a, b, builtIns);
    }
    if (j != null && joinNeedsNonNullConstraint && !j.IsNonNullRefType) {
      // try to make j into a non-null type; if that's not possible, then there is no meet
      var udt = j as UserDefinedType;
      if (udt != null && udt.ResolvedClass is ClassDecl) {
        // add the non-null constraint back in
        j = UserDefinedType.CreateNonNullType(udt);
      } else {
        // the original a and b have no meet
        j = null;
      }
    }
    if (DafnyOptions.O.TypeInferenceDebug) {
      Console.WriteLine("DEBUG: Meet( {0}, {1} ) = {2}", a, b, j);
    }
    return j;
  }
  public static Type MeetX(Type a, Type b, BuiltIns builtIns) {
    Contract.Requires(a != null);
    Contract.Requires(b != null);
    Contract.Requires(builtIns != null);

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
        var typeArgs = ComputeExtrema(directions, a.TypeArgs, b.TypeArgs, builtIns);
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
      return a.Equals(b) ? a : null;
    } else if (a is SetType) {
      var aa = (SetType)a;
      var bb = b as SetType;
      if (bb == null || aa.Finite != bb.Finite) {
        return null;
      }
      // sets are co-variant in their argument type
      var typeArg = Meet(a.TypeArgs[0], b.TypeArgs[0], builtIns);
      return typeArg == null ? null : new SetType(aa.Finite, typeArg);
    } else if (a is MultiSetType) {
      var aa = (MultiSetType)a;
      var bb = b as MultiSetType;
      if (bb == null) {
        return null;
      }
      // multisets are co-variant in their argument type
      var typeArg = Meet(a.TypeArgs[0], b.TypeArgs[0], builtIns);
      return typeArg == null ? null : new MultiSetType(typeArg);
    } else if (a is SeqType) {
      var aa = (SeqType)a;
      var bb = b as SeqType;
      if (bb == null) {
        return null;
      }
      // sequences are co-variant in their argument type
      var typeArg = Meet(a.TypeArgs[0], b.TypeArgs[0], builtIns);
      return typeArg == null ? null : new SeqType(typeArg);
    } else if (a is MapType) {
      var aa = (MapType)a;
      var bb = b as MapType;
      if (bb == null || aa.Finite != bb.Finite) {
        return null;
      }
      // maps are co-variant in both argument types
      var typeArgDomain = Meet(a.TypeArgs[0], b.TypeArgs[0], builtIns);
      var typeArgRange = Meet(a.TypeArgs[1], b.TypeArgs[1], builtIns);
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
      var typeArgs = ComputeExtrema(directions, a.TypeArgs, b.TypeArgs, builtIns);
      if (typeArgs == null) {
        return null;
      }
      var udt = (UserDefinedType)a;
      return new UserDefinedType(udt.tok, udt.Name, aa, typeArgs);
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
      var typeArgs = ComputeExtrema(directions, a.TypeArgs, b.TypeArgs, builtIns);
      if (typeArgs == null) {
        return null;
      }
      var arr = (ArrowType)aa;
      return new ArrowType(arr.tok, (ArrowTypeDecl)arr.ResolvedClass, typeArgs);
    } else if (b.IsObjectQ) {
      return a.IsRefType ? a : null;
    } else if (a.IsObjectQ) {
      return b.IsRefType ? b : null;
    } else {
      // "a" is a class, trait, or opaque type
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
        var typeArgs = ComputeExtrema(directions, a.TypeArgs, b.TypeArgs, builtIns);
        if (typeArgs == null) {
          return null;
        }
        var udt = (UserDefinedType)a;
        return new UserDefinedType(udt.tok, udt.Name, aa, typeArgs);
      } else if (aa is ClassDecl && bb is ClassDecl) {
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

  public virtual List<Type> ParentTypes() {
    return new List<Type>();
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

    return sub.ParentTypes().Any(parentType => parentType.IsSubtypeOf(super, ignoreTypeArguments, ignoreNullity));
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
  [Pure]
  public override string TypeName(ModuleDefinition context, bool parseAble) {
    return "int";
  }
  public override bool Equals(Type that, bool keepConstraints = false) {
    return keepConstraints ? this.GetType() == that.GetType() : that is IntVarietiesSupertype;
  }
}
public class RealVarietiesSupertype : ArtificialType {
  [Pure]
  public override string TypeName(ModuleDefinition context, bool parseAble) {
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
}

public abstract class BasicType : NonProxyType {
  public override IEnumerable<INode> Children => Enumerable.Empty<INode>();
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
  [Pure]
  public override string TypeName(ModuleDefinition context, bool parseAble) {
    return "bool";
  }
  public override bool Equals(Type that, bool keepConstraints = false) {
    return that.IsBoolType;
  }
}

public class CharType : BasicType {
  public const char DefaultValue = 'D';
  public const string DefaultValueAsString = "'D'";
  [Pure]
  public override string TypeName(ModuleDefinition context, bool parseAble) {
    return "char";
  }
  public override bool Equals(Type that, bool keepConstraints = false) {
    return that.IsCharType;
  }
}

public class IntType : BasicType {
  [Pure]
  public override string TypeName(ModuleDefinition context, bool parseAble) {
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
  [Pure]
  public override string TypeName(ModuleDefinition context, bool parseAble) {
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
  [Pure]
  public override string TypeName(ModuleDefinition context, bool parseAble) {
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
  public BitvectorType(int width)
    : base() {
    Contract.Requires(0 <= width);
    Width = width;
    foreach (var nativeType in Resolver.NativeTypes) {
      if (DafnyOptions.O.Compiler.SupportedNativeTypes.Contains(nativeType.Name) && width <= nativeType.Bitwidth) {
        NativeType = nativeType;
        break;
      }
    }
  }

  [Pure]
  public override string TypeName(ModuleDefinition context, bool parseAble) {
    return "bv" + Width;
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
    TypeArg = new TypeParameter(Token.NoToken, "selfType", TypeParameter.TPVarianceSyntax.NonVariant_Strict);
  }

  [Pure]
  public override string TypeName(ModuleDefinition context, bool parseAble) {
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
  public override IEnumerable<INode> Nodes => TypeArgs.SelectMany(ta => ta.Nodes);

  public override string TypeName(ModuleDefinition context, bool parseAble) {
    Contract.Ensures(Contract.Result<string>() != null);
    var targs = HasTypeArg() ? this.TypeArgsToString(context, parseAble) : "";
    return CollectionTypeName + targs;
  }
  public Type Arg {
    get {
      Contract.Ensures(Contract.Result<Type>() != null);  // this is true only after "arg" has really been set (i.e., it follows from the precondition)
      Contract.Assume(arg != null);  // This is really a precondition.  Don't call Arg until "arg" has been set.
      return arg;
    }
  }  // denotes the Domain type for a Map
  private Type arg;
  // The following methods, HasTypeArg and SetTypeArg/SetTypeArgs, are to be called during resolution to make sure that "arg" becomes set.
  public bool HasTypeArg() {
    return arg != null;
  }
  public void SetTypeArg(Type arg) {
    Contract.Requires(arg != null);
    Contract.Requires(1 <= this.TypeArgs.Count);  // this is actually an invariant of all collection types
    Contract.Assume(this.arg == null);  // Can only set it once.  This is really a precondition.
    this.arg = arg;
    this.TypeArgs[0] = arg;
  }
  public virtual void SetTypeArgs(Type arg, Type other) {
    Contract.Requires(arg != null);
    Contract.Requires(other != null);
    Contract.Requires(this.TypeArgs.Count == 2);
    Contract.Assume(this.arg == null);  // Can only set it once.  This is really a precondition.
    this.arg = arg;
    this.TypeArgs[0] = arg;
    this.TypeArgs[1] = other;
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
    this.TypeArgs = new List<Type> { arg };
  }
  /// <summary>
  /// This constructor is a collection types with 2 type arguments
  /// </summary>
  protected CollectionType(Type arg, Type other) {
    this.arg = arg;
    this.TypeArgs = new List<Type> { arg, other };
  }

  public override bool ComputeMayInvolveReferences(ISet<DatatypeDecl> visitedDatatypes) {
    return Arg.ComputeMayInvolveReferences(visitedDatatypes);
  }
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
  [Pure]
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
}
public class MapType : CollectionType {
  public bool Finite {
    get { return finite; }
    set { finite = value; }
  }
  private bool finite;
  public Type Range {
    get { return range; }
  }
  private Type range;
  public override void SetTypeArgs(Type domain, Type range) {
    base.SetTypeArgs(domain, range);
    Contract.Assume(this.range == null);  // Can only set once.  This is really a precondition.
    this.range = range;
  }
  public MapType(bool finite, Type domain, Type range) : base(domain, range) {
    Contract.Requires((domain == null && range == null) || (domain != null && range != null));
    this.finite = finite;
    this.range = range;
  }
  public Type Domain {
    get { return Arg; }
  }
  public override string CollectionTypeName { get { return finite ? "map" : "imap"; } }
  [Pure]
  public override string TypeName(ModuleDefinition context, bool parseAble) {
    Contract.Ensures(Contract.Result<string>() != null);
    var targs = HasTypeArg() ? this.TypeArgsToString(context, parseAble) : "";
    return CollectionTypeName + targs;
  }
  public override bool Equals(Type that, bool keepConstraints = false) {
    var t = that.NormalizeExpand(keepConstraints) as MapType;
    return t != null && Finite == t.Finite && Arg.Equals(t.Arg, keepConstraints) && Range.Equals(t.Range, keepConstraints);
  }

  public override Type Subst(IDictionary<TypeParameter, Type> subst) {
    var dom = Domain.Subst(subst);
    if (dom is InferredTypeProxy) {
      ((InferredTypeProxy)dom).KeepConstraints = true;
    }
    var ran = Range.Subst(subst);
    if (ran is InferredTypeProxy) {
      ((InferredTypeProxy)ran).KeepConstraints = true;
    }
    if (dom == Domain && ran == Range) {
      return this;
    } else {
      return new MapType(Finite, dom, ran);
    }
  }

  public override Type ReplaceTypeArguments(List<Type> arguments) {
    return new MapType(Finite, arguments[0], arguments[1]);
  }

  public override bool SupportsEquality {
    get {
      // A map type supports equality if both its Keys type and Values type does.  It is checked
      // that the Keys type always supports equality, so we only need to check the Values type here.
      return range.SupportsEquality;
    }
  }
  public override bool ComputeMayInvolveReferences(ISet<DatatypeDecl> visitedDatatypes) {
    return Domain.ComputeMayInvolveReferences(visitedDatatypes) || Range.ComputeMayInvolveReferences(visitedDatatypes);
  }
}

public class UserDefinedType : NonProxyType {
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(tok != null);
    Contract.Invariant(Name != null);
    Contract.Invariant(cce.NonNullElements(TypeArgs));
    Contract.Invariant(NamePath is NameSegment || NamePath is ExprDotName);
    Contract.Invariant(!ArrowType.IsArrowTypeName(Name) || this is ArrowType);
  }

  public readonly Expression NamePath;  // either NameSegment or ExprDotName (with the inner expression satisfying this same constraint)
  public readonly string Name;
  [Rep]

  public string FullName {
    get {
      if (ResolvedClass?.EnclosingModuleDefinition?.IsDefaultModule == false) {
        return ResolvedClass.EnclosingModuleDefinition.Name + "." + Name;
      } else {
        return Name;
      }
    }
  }

  string compileName;
  public string CompileName => compileName ??= ResolvedClass.CompileName;

  public string FullCompanionCompileName {
    get {
      Contract.Requires(ResolvedClass is TraitDecl || (ResolvedClass is NonNullTypeDecl nntd && nntd.Class is TraitDecl));
      var m = ResolvedClass.EnclosingModuleDefinition;
      var s = m.IsDefaultModule ? "" : m.CompileName + ".";
      return s + "_Companion_" + ResolvedClass.CompileName;
    }
  }

  [FilledInDuringResolution] public TopLevelDecl ResolvedClass;  // if Name denotes a class/datatype/iterator and TypeArgs match the type parameters of that class/datatype/iterator

  public UserDefinedType(IToken tok, string name, List<Type> optTypeArgs)
    : this(tok, new NameSegment(tok, name, optTypeArgs)) {
    Contract.Requires(tok != null);
    Contract.Requires(name != null);
    Contract.Requires(optTypeArgs == null || optTypeArgs.Count > 0);  // this is what it means to be syntactically optional
  }

  public UserDefinedType(IToken tok, Expression namePath) {
    Contract.Requires(tok != null);
    Contract.Requires(namePath is NameSegment || namePath is ExprDotName);
    this.tok = tok;
    if (namePath is NameSegment) {
      var n = (NameSegment)namePath;
      this.Name = n.Name;
      this.TypeArgs = n.OptTypeArguments;
    } else {
      var n = (ExprDotName)namePath;
      this.Name = n.SuffixName;
      this.TypeArgs = n.OptTypeArguments;
    }
    if (this.TypeArgs == null) {
      this.TypeArgs = new List<Type>();  // TODO: is this really the thing to do?
    }
    this.NamePath = namePath;
  }

  public UserDefinedType(Cloner cloner, UserDefinedType original)
    : this(cloner.Tok(original.tok), cloner.CloneExpr(original.NamePath)) {
    if (cloner.CloneResolvedFields) {
      ResolvedClass = original.ResolvedClass;
    }
  }

  /// <summary>
  /// Constructs a Type (in particular, a UserDefinedType) from a TopLevelDecl denoting a type declaration.  If
  /// the given declaration takes type parameters, these are filled as references to the formal type parameters
  /// themselves.  (Usually, this method is called when the type parameters in the result don't matter, other
  /// than that they need to be filled in, so as to make a properly resolved UserDefinedType.)
  /// If "typeArgs" is non-null, then its type parameters are used in constructing the returned type.
  /// If "typeArgs" is null, then the formal type parameters of "cd" are used.
  /// </summary>
  public static UserDefinedType FromTopLevelDecl(IToken tok, TopLevelDecl cd, List<TypeParameter> typeArgs = null) {
    Contract.Requires(tok != null);
    Contract.Requires(cd != null);
    Contract.Assert((cd is ArrowTypeDecl) == ArrowType.IsArrowTypeName(cd.Name));
    var args = (typeArgs ?? cd.TypeArgs).ConvertAll(tp => (Type)new UserDefinedType(tp));
    if (cd is ArrowTypeDecl) {
      return new ArrowType(tok, (ArrowTypeDecl)cd, args);
    } else if (cd is ClassDecl && !(cd is DefaultClassDecl)) {
      return new UserDefinedType(tok, cd.Name + "?", cd, args);
    } else {
      return new UserDefinedType(tok, cd.Name, cd, args);
    }
  }

  public static UserDefinedType FromTopLevelDeclWithAllBooleanTypeParameters(TopLevelDecl cd) {
    Contract.Requires(cd != null);
    Contract.Requires(!(cd is ArrowTypeDecl));

    var typeArgs = cd.TypeArgs.ConvertAll(tp => (Type)Type.Bool);
    return new UserDefinedType(cd.tok, cd.Name, cd, typeArgs);
  }

  /// <summary>
  /// If "member" is non-null, then:
  ///   Return the upcast of "receiverType" that has base type "member.EnclosingClass".
  ///   Assumes that "receiverType" normalizes to a UserDefinedFunction with a .ResolveClass that is a subtype
  ///   of "member.EnclosingClass".
  /// Otherwise:
  ///   Return "receiverType" (expanded).
  /// </summary>
  public static Type UpcastToMemberEnclosingType(Type receiverType, MemberDecl/*?*/ member) {
    Contract.Requires(receiverType != null);
    if (member != null && member.EnclosingClass != null && !(member.EnclosingClass is ValuetypeDecl)) {
      return receiverType.AsParentType(member.EnclosingClass);
    }
    return receiverType.NormalizeExpandKeepConstraints();
  }

  /// <summary>
  /// This constructor constructs a resolved class/datatype/iterator/subset-type/newtype type
  /// </summary>
  public UserDefinedType(IToken tok, string name, TopLevelDecl cd, [Captured] List<Type> typeArgs, Expression/*?*/ namePath = null) {
    Contract.Requires(tok != null);
    Contract.Requires(name != null);
    Contract.Requires(cd != null);
    Contract.Requires(cce.NonNullElements(typeArgs));
    Contract.Requires(cd.TypeArgs.Count == typeArgs.Count);
    Contract.Requires(namePath == null || namePath is NameSegment || namePath is ExprDotName);
    // The following is almost a precondition. In a few places, the source program names a class, not a type,
    // and in then name==cd.Name for a ClassDecl.
    //Contract.Requires(!(cd is ClassDecl) || cd is DefaultClassDecl || cd is ArrowTypeDecl || name == cd.Name + "?");
    Contract.Requires(!(cd is ArrowTypeDecl) || name == cd.Name);
    Contract.Requires(!(cd is DefaultClassDecl) || name == cd.Name);
    this.tok = tok;
    this.Name = name;
    this.ResolvedClass = cd;
    this.TypeArgs = typeArgs;
    if (namePath == null) {
      var ns = new NameSegment(tok, name, typeArgs.Count == 0 ? null : typeArgs);
      var r = new Resolver_IdentifierExpr(tok, cd, typeArgs);
      ns.ResolvedExpression = r;
      ns.Type = r.Type;
      this.NamePath = ns;
    } else {
      this.NamePath = namePath;
    }
  }

  public static UserDefinedType CreateNonNullType(UserDefinedType udtNullableType) {
    Contract.Requires(udtNullableType != null);
    Contract.Requires(udtNullableType.ResolvedClass is ClassDecl);
    var cl = (ClassDecl)udtNullableType.ResolvedClass;
    return new UserDefinedType(udtNullableType.tok, cl.NonNullTypeDecl.Name, cl.NonNullTypeDecl, udtNullableType.TypeArgs);
  }

  public static UserDefinedType CreateNullableType(UserDefinedType udtNonNullType) {
    Contract.Requires(udtNonNullType != null);
    Contract.Requires(udtNonNullType.ResolvedClass is NonNullTypeDecl);
    var nntd = (NonNullTypeDecl)udtNonNullType.ResolvedClass;
    return new UserDefinedType(udtNonNullType.tok, nntd.Class.Name + "?", nntd.Class, udtNonNullType.TypeArgs);
  }

  /// <summary>
  /// This constructor constructs a resolved type parameter
  /// </summary>
  public UserDefinedType(TypeParameter tp)
    : this(tp.tok, tp) {
    Contract.Requires(tp != null);
  }

  /// <summary>
  /// This constructor constructs a resolved type parameter (but shouldn't be called if "tp" denotes
  /// the .TheType of an opaque type -- use the (OpaqueType_AsParameter, OpaqueTypeDecl, List(Type))
  /// constructor for that).
  /// </summary>
  public UserDefinedType(IToken tok, TypeParameter tp) {
    Contract.Requires(tok != null);
    Contract.Requires(tp != null);
    this.tok = tok;
    this.Name = tp.Name;
    this.TypeArgs = new List<Type>();
    this.ResolvedClass = tp;
    var ns = new NameSegment(tok, tp.Name, null);
    var r = new Resolver_IdentifierExpr(tok, tp);
    ns.ResolvedExpression = r;
    ns.Type = r.Type;
    this.NamePath = ns;
  }

  public override bool Equals(Type that, bool keepConstraints = false) {
    var i = NormalizeExpand(keepConstraints);
    if (i is UserDefinedType) {
      var ii = (UserDefinedType)i;
      var t = that.NormalizeExpand(keepConstraints) as UserDefinedType;
      if (t == null || ii.ResolvedClass != t.ResolvedClass || ii.TypeArgs.Count != t.TypeArgs.Count) {
        return false;
      } else {
        for (int j = 0; j < ii.TypeArgs.Count; j++) {
          if (!ii.TypeArgs[j].Equals(t.TypeArgs[j], keepConstraints)) {
            return false;
          }
        }
        return true;
      }
    } else {
      // TODO?: return i.Equals(that.NormalizeExpand());
      return i.Equals(that, keepConstraints);
    }
  }

  public override Type Subst(IDictionary<TypeParameter, Type> subst) {
    if (ResolvedClass is TypeParameter tp) {
      if (subst.TryGetValue(tp, out var s)) {
        Contract.Assert(TypeArgs.Count == 0);
        return s;
      } else {
        return this;
      }
    } else if (ResolvedClass != null) {
      List<Type> newArgs = null;  // allocate it lazily
      var resolvedClass = ResolvedClass;
      var isArrowType = ArrowType.IsPartialArrowTypeName(resolvedClass.Name) || ArrowType.IsTotalArrowTypeName(resolvedClass.Name);
      for (int i = 0; i < TypeArgs.Count; i++) {
        Type p = TypeArgs[i];
        Type s = p.Subst(subst);
        if (s is InferredTypeProxy && !isArrowType) {
          ((InferredTypeProxy)s).KeepConstraints = true;
        }
        if (s != p && newArgs == null) {
          // lazily construct newArgs
          newArgs = new List<Type>();
          for (int j = 0; j < i; j++) {
            newArgs.Add(TypeArgs[j]);
          }
        }
        if (newArgs != null) {
          newArgs.Add(s);
        }
      }
      if (newArgs == null) {
        // there were no substitutions
        return this;
      } else {
        // Note, even if t.NamePath is non-null, we don't care to keep that syntactic part of the expression in what we return here
        return new UserDefinedType(tok, Name, resolvedClass, newArgs);
      }
    } else {
      // there's neither a resolved param nor a resolved class, which means the UserDefinedType wasn't
      // properly resolved; just return it
      return this;
    }
  }

  public override Type ReplaceTypeArguments(List<Type> arguments) {
    return new UserDefinedType(tok, Name, ResolvedClass, arguments);
  }

  /// <summary>
  /// If type denotes a resolved class type, then return that class type.
  /// Otherwise, return null.
  /// </summary>
  public static UserDefinedType DenotesClass(Type type) {
    Contract.Requires(type != null);
    Contract.Ensures(Contract.Result<UserDefinedType>() == null || Contract.Result<UserDefinedType>().ResolvedClass is ClassDecl);
    type = type.NormalizeExpand();
    UserDefinedType ct = type as UserDefinedType;
    if (ct != null && ct.ResolvedClass is ClassDecl) {
      return ct;
    } else {
      return null;
    }
  }

  public static Type ArrayElementType(Type type) {
    Contract.Requires(type != null);
    Contract.Requires(type.IsArrayType);
    Contract.Ensures(Contract.Result<Type>() != null);

    UserDefinedType udt = DenotesClass(type);
    Contract.Assert(udt != null);
    Contract.Assert(udt.TypeArgs.Count == 1);  // holds true of all array types
    return udt.TypeArgs[0];
  }

  public override IEnumerable<INode> Nodes => new[] { this }.Concat(TypeArgs.SelectMany(t => t.Nodes));

  [Pure]
  public override string TypeName(ModuleDefinition context, bool parseAble) {
    Contract.Ensures(Contract.Result<string>() != null);
    if (BuiltIns.IsTupleTypeName(Name)) {
      // Unfortunately, ResolveClass may be null, so Name is all we have.  Reverse-engineer the string name.
      IEnumerable<bool> argumentGhostness = BuiltIns.ArgumentGhostnessFromString(Name, TypeArgs.Count);
      return "(" + Util.Comma(System.Linq.Enumerable.Zip(TypeArgs, argumentGhostness),
        (ty_u) => Resolver.GhostPrefix(ty_u.Item2) + ty_u.Item1.TypeName(context, parseAble)) + ")";
    } else if (ArrowType.IsPartialArrowTypeName(Name)) {
      return ArrowType.PrettyArrowTypeName(ArrowType.PARTIAL_ARROW, TypeArgs, null, context, parseAble);
    } else if (ArrowType.IsTotalArrowTypeName(Name)) {
      return ArrowType.PrettyArrowTypeName(ArrowType.TOTAL_ARROW, TypeArgs, null, context, parseAble);
    } else {
#if TEST_TYPE_SYNONYM_TRANSPARENCY
        if (Name == "type#synonym#transparency#test" && ResolvedClass is TypeSynonymDecl) {
          return ((TypeSynonymDecl)ResolvedClass).Rhs.TypeName(context);
        }
#endif
      var s = Printer.ExprToString(NamePath);
      if (ResolvedClass != null) {
        var optionalTypeArgs = NamePath is NameSegment ? ((NameSegment)NamePath).OptTypeArguments : ((ExprDotName)NamePath).OptTypeArguments;
        if (optionalTypeArgs == null && TypeArgs != null && TypeArgs.Count != 0) {
          s += this.TypeArgsToString(context, parseAble);
        }
      }
      return s;
    }
  }

  public override bool SupportsEquality {
    get {
      if (ResolvedClass is ClassDecl || ResolvedClass is NewtypeDecl) {
        return ResolvedClass.IsRevealedInScope(Type.GetScope());
      } else if (ResolvedClass is CoDatatypeDecl) {
        return false;
      } else if (ResolvedClass is IndDatatypeDecl) {
        var dt = (IndDatatypeDecl)ResolvedClass;
        Contract.Assume(dt.EqualitySupport != IndDatatypeDecl.ES.NotYetComputed);
        if (!dt.IsRevealedInScope(Type.GetScope())) {
          return false;
        }
        if (dt.EqualitySupport == IndDatatypeDecl.ES.Never) {
          return false;
        }
        Contract.Assert(dt.TypeArgs.Count == TypeArgs.Count);
        var i = 0;
        foreach (var tp in dt.TypeArgs) {
          if (tp.NecessaryForEqualitySupportOfSurroundingInductiveDatatype && !TypeArgs[i].SupportsEquality) {
            return false;
          }
          i++;
        }
        return true;
      } else if (ResolvedClass is TypeSynonymDeclBase) {
        var t = (TypeSynonymDeclBase)ResolvedClass;
        if (t.SupportsEquality) {
          return true;
        } else if (t.IsRevealedInScope(Type.GetScope())) {
          return t.RhsWithArgument(TypeArgs).SupportsEquality;
        } else {
          return false;
        }
      } else if (ResolvedClass is TypeParameter) {
        return ((TypeParameter)ResolvedClass).SupportsEquality;
      } else if (ResolvedClass is OpaqueTypeDecl) {
        return ((OpaqueTypeDecl)ResolvedClass).SupportsEquality;
      }
      Contract.Assume(false);  // the SupportsEquality getter requires the Type to have been successfully resolved
      return true;
    }
  }

  public override bool PartiallySupportsEquality {
    get {
      var totalEqualitySupport = SupportsEquality;
      if (!totalEqualitySupport && ResolvedClass is TypeSynonymDeclBase synonymBase) {
        return synonymBase.IsRevealedInScope(Type.GetScope()) && synonymBase.RhsWithArgument(TypeArgs).PartiallySupportsEquality;
      } else if (!totalEqualitySupport && ResolvedClass is IndDatatypeDecl dt && dt.IsRevealedInScope(Type.GetScope())) {
        // Equality is partially supported (at run time) for a datatype that
        //   * is inductive (because codatatypes never support equality), and
        //   * has at least one non-ghost constructor (because if all constructors are ghost, then equality is never supported), and
        //   * for each non-ghost constructor, every argument totally supports equality (an argument totally supports equality
        //       if it is non-ghost (because ghost arguments are not available at run time) and has a type that supports equality).
        var hasNonGhostConstructor = false;
        foreach (var ctor in dt.Ctors.Where(ctor => !ctor.IsGhost)) {
          hasNonGhostConstructor = true;
          if (!ctor.Formals.All(formal => !formal.IsGhost && formal.Type.SupportsEquality)) {
            return false;
          }
        }
        Contract.Assert(dt.HasGhostVariant); // sanity check (if the types of all formals support equality, then either .SupportsEquality or there is a ghost constructor)
        return hasNonGhostConstructor;
      }
      return totalEqualitySupport;
    }
  }

  public override bool ComputeMayInvolveReferences(ISet<DatatypeDecl> visitedDatatypes) {
    if (ResolvedClass is ArrowTypeDecl) {
      return TypeArgs.Any(ta => ta.ComputeMayInvolveReferences(visitedDatatypes));
    } else if (ResolvedClass is ClassDecl) {
      return true;
    } else if (ResolvedClass is NewtypeDecl) {
      return false;
    } else if (ResolvedClass is DatatypeDecl) {
      // Datatype declarations do not support explicit (!new) annotations. Instead, whether or not
      // a datatype involves references depends on the definition and parametrization of the type.
      // See ComputeMayInvolveReferences in class Type for more information.
      // In particular, if one of the datatype's constructors mentions a type that involves
      // references, then so does the datatype. And if one of the datatype's type arguments involves
      // references, then we consider the datatype to do so as well (without regard to whether or
      // not the type parameter is actually used in the definition of the datatype).
      var dt = (DatatypeDecl)ResolvedClass;
      if (!dt.IsRevealedInScope(Type.GetScope())) {
        // The type's definition is hidden from the current scope, so we
        // have to assume the type may involve references.
        return true;
      } else if (TypeArgs.Any(ta => ta.ComputeMayInvolveReferences(visitedDatatypes))) {
        return true;
      } else if (visitedDatatypes != null && visitedDatatypes.Contains(dt)) {
        // we're in the middle of looking through the types involved in dt's definition
        return false;
      } else {
        visitedDatatypes ??= new HashSet<DatatypeDecl>();
        visitedDatatypes.Add(dt);
        return dt.Ctors.Any(ctor => ctor.Formals.Any(f => f.Type.ComputeMayInvolveReferences(visitedDatatypes)));
      }
    } else if (ResolvedClass is TypeSynonymDeclBase) {
      var t = (TypeSynonymDeclBase)ResolvedClass;
      if (t.Characteristics.ContainsNoReferenceTypes) {
        // There's an explicit "(!new)" annotation on the type.
        return false;
      } else if (t.IsRevealedInScope(Type.GetScope())) {
        // The type's definition is available in the scope, so consult the RHS type
        return t.RhsWithArgument(TypeArgs).ComputeMayInvolveReferences(visitedDatatypes);
      } else {
        // The type's definition is hidden from the current scope and there's no explicit "(!new)", so we
        // have to assume the type may involve references.
        return true;
      }
    } else if (ResolvedClass is TypeParameter typeParameter) {
      if (visitedDatatypes != null) {
        // Datatypes look at the type arguments passed in, so we ignore their formal type parameters.
        // See comment above and in Type.ComputeMayInvolveReferences.
        Contract.Assert(typeParameter.Parent is DatatypeDecl);
        return false;
      } else {
        return !typeParameter.Characteristics.ContainsNoReferenceTypes;
      }
    } else if (ResolvedClass is OpaqueTypeDecl opaqueTypeDecl) {
      return !opaqueTypeDecl.Characteristics.ContainsNoReferenceTypes;
    }
    Contract.Assume(false);  // unexpected or not successfully resolved Type
    return true;
  }

  public override List<Type> ParentTypes() {
    return ResolvedClass != null ? ResolvedClass.ParentTypes(TypeArgs) : base.ParentTypes();
  }

  public override bool IsSubtypeOf(Type super, bool ignoreTypeArguments, bool ignoreNullity) {
    super = super.NormalizeExpandKeepConstraints();

    // Specifically handle object as the implicit supertype of classes and traits.
    // "object?" is handled by Builtins rather than the Type hierarchy, so unfortunately
    // it can't be returned in ParentTypes().
    if (super.IsObjectQ) {
      return IsRefType;
    } else if (super.IsObject) {
      return ignoreNullity ? IsRefType : IsNonNullRefType;
    }

    return base.IsSubtypeOf(super, ignoreTypeArguments, ignoreNullity);
  }

  public IToken NameToken => tok;
  public override IEnumerable<INode> Children => base.Children.Concat(new[] { NamePath });
}

public abstract class TypeProxy : Type {
  public override IEnumerable<INode> Children => Enumerable.Empty<INode>();
  [FilledInDuringResolution] public Type T;
  public readonly List<TypeConstraint> SupertypeConstraints = new List<TypeConstraint>();
  public readonly List<TypeConstraint> SubtypeConstraints = new List<TypeConstraint>();

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

  public IEnumerable<Type> SubtypesKeepConstraints_WithAssignable(List<Resolver.XConstraint> allXConstraints) {
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
    Contract.Ensures(Contract.Result<Family>() != Family.Unknown || t is TypeProxy || t is Resolver_IdentifierExpr.ResolverType);  // return Unknown ==> t is TypeProxy || t is ResolverType
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
    } else if (t.IsTypeParameter || t.IsOpaqueType || t.IsInternalTypeSynonym) {
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
  [Pure]
  public override string TypeName(ModuleDefinition context, bool parseAble) {
    Contract.Ensures(Contract.Result<string>() != null);
#if TI_DEBUG_PRINT
    if (DafnyOptions.O.TypeInferenceDebug) {
      return T == null ? "?" + id : T.TypeName(context);
    }
#endif
    return T == null ? "?" : T.TypeName(context, parseAble);
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

  [Pure]
  internal static bool IsSupertypeOfLiteral(Type t) {
    Contract.Requires(t != null);
    return t is ArtificialType;
  }
  internal Type InClusterOfArtificial(List<Resolver.XConstraint> allXConstraints) {
    Contract.Requires(allXConstraints != null);
    return InClusterOfArtificial_aux(new HashSet<TypeProxy>(), allXConstraints);
  }
  private Type InClusterOfArtificial_aux(ISet<TypeProxy> visitedProxies, List<Resolver.XConstraint> allXConstraints) {
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
  public override IEnumerable<INode> Children => Enumerable.Empty<INode>();
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
