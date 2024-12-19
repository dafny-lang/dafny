using System.Collections.Generic;
using System.Diagnostics.Contracts;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny;

public class TypeParameter : TopLevelDecl {
  public interface ParentType {
    string FullName { get; }
    IOrigin Tok { get; }
  }

  public override string WhatKind => "type parameter";

  public bool IsAutoCompleted => Name.StartsWith("_");

  ParentType parent;
  public ParentType Parent {
    get {
      return parent;
    }
    set {
      Contract.Requires(Parent == null);  // set it only once
      Contract.Requires(value != null);
      parent = value;
    }
  }

  public override string SanitizedName {
    get {
      if (sanitizedName == null) {
        var name = Name;
        if (parent is MemberDecl && !name.StartsWith("_")) {
          // prepend "_" to type parameters of functions and methods, to ensure they don't clash with type parameters of the enclosing type
          name = "_" + name;
        }
        sanitizedName = NonglobalVariable.SanitizeName(name);
      }
      return sanitizedName;
    }
  }

  public override string GetCompileName(DafnyOptions options) => SanitizedName;

  /// <summary>
  /// NonVariant_Strict     (default) - non-variant, no uses left of an arrow
  /// NonVariant_Permissive    !      - non-variant
  /// Covariant_Strict         +      - co-variant, no uses left of an arrow
  /// Covariant_Permissive     *      - co-variant
  /// Contravariant            -      - contra-variant
  /// </summary>
  public enum TPVarianceSyntax { NonVariant_Strict, NonVariant_Permissive, Covariant_Strict, Covariant_Permissive, Contravariance }
  public static string VarianceString(TPVarianceSyntax varianceSyntax) {
    switch (varianceSyntax) {
      case TPVarianceSyntax.NonVariant_Strict: return "";
      case TPVarianceSyntax.NonVariant_Permissive: return "!";
      case TPVarianceSyntax.Covariant_Strict: return "+";
      case TPVarianceSyntax.Covariant_Permissive: return "*";
      case TPVarianceSyntax.Contravariance: return "-";
    }
    return ""; // Should not happen, but compiler complains
  }
  public enum TPVariance { Co, Non, Contra }
  public static TPVariance Negate(TPVariance v) {
    switch (v) {
      case TPVariance.Co:
        return TPVariance.Contra;
      case TPVariance.Contra:
        return TPVariance.Co;
      default:
        return v;
    }
  }
  public static int Direction(TPVariance v) {
    switch (v) {
      case TPVariance.Co:
        return 1;
      case TPVariance.Contra:
        return -1;
      default:
        return 0;
    }
  }
  public TPVarianceSyntax VarianceSyntax;
  public TPVariance Variance {
    get {
      switch (VarianceSyntax) {
        case TPVarianceSyntax.Covariant_Strict:
        case TPVarianceSyntax.Covariant_Permissive:
          return TPVariance.Co;
        case TPVarianceSyntax.NonVariant_Strict:
        case TPVarianceSyntax.NonVariant_Permissive:
          return TPVariance.Non;
        case TPVarianceSyntax.Contravariance:
          return TPVariance.Contra;
        default:
          Contract.Assert(false);  // unexpected VarianceSyntax
          throw new cce.UnreachableException();
      }
    }
  }
  public bool StrictVariance {
    get {
      switch (VarianceSyntax) {
        case TPVarianceSyntax.Covariant_Strict:
        case TPVarianceSyntax.NonVariant_Strict:
          return true;
        case TPVarianceSyntax.Covariant_Permissive:
        case TPVarianceSyntax.NonVariant_Permissive:
        case TPVarianceSyntax.Contravariance:
          return false;
        default:
          Contract.Assert(false);  // unexpected VarianceSyntax
          throw new cce.UnreachableException();
      }
    }
  }

  public static List<TPVariance> Variances(List<TypeParameter> typeParameters, bool negate = false) {
    if (negate) {
      return typeParameters.ConvertAll(tp => Negate(tp.Variance));
    } else {
      return typeParameters.ConvertAll(tp => tp.Variance);
    }
  }

  public enum EqualitySupportValue { Required, InferredRequired, Unspecified }
  public struct TypeParameterCharacteristics {
    public SourceOrigin SourceOrigin = null;
    public EqualitySupportValue EqualitySupport;  // the resolver may change this value from Unspecified to InferredRequired (for some signatures that may immediately imply that equality support is required)
    public Type.AutoInitInfo AutoInit;
    public bool HasCompiledValue => AutoInit == Type.AutoInitInfo.CompilableValue;
    public bool IsNonempty => AutoInit != Type.AutoInitInfo.MaybeEmpty;
    public bool ContainsNoReferenceTypes;
    public TypeParameterCharacteristics(bool dummy) {
      EqualitySupport = EqualitySupportValue.Unspecified;
      AutoInit = Type.AutoInitInfo.MaybeEmpty;
      ContainsNoReferenceTypes = false;
    }
    public TypeParameterCharacteristics(EqualitySupportValue eqSupport, Type.AutoInitInfo autoInit, bool containsNoReferenceTypes) {
      EqualitySupport = eqSupport;
      AutoInit = autoInit;
      ContainsNoReferenceTypes = containsNoReferenceTypes;
    }
    public override string ToString() {
      string result = "";
      if (EqualitySupport == EqualitySupportValue.Required) {
        result += ",==";
      }
      if (HasCompiledValue) {
        result += ",0";
      }
      if (AutoInit == Type.AutoInitInfo.Nonempty) {
        result += ",00";
      }
      if (ContainsNoReferenceTypes) {
        result += ",!new";
      }
      if (result.Length != 0) {
        result = "(" + result.Substring(1) + ")";
      }
      return result;
    }
  }
  public TypeParameterCharacteristics Characteristics;
  public bool SupportsEquality {
    get { return Characteristics.EqualitySupport != EqualitySupportValue.Unspecified; }
  }

  public bool NecessaryForEqualitySupportOfSurroundingInductiveDatatype = false;  // computed during resolution; relevant only when Parent denotes an IndDatatypeDecl

  public bool IsToplevelScope { // true if this type parameter is on a toplevel (ie. class C<T>), and false if it is on a member (ie. method m<T>(...))
    get { return parent is TopLevelDecl; }
  }
  public int PositionalIndex; // which type parameter this is (ie. in C<S, T, U>, S is 0, T is 1 and U is 2).

  public readonly List<Type> TypeBounds;

  public IEnumerable<TopLevelDecl> TypeBoundHeads {
    get {
      foreach (var typeBound in TypeBounds) {
        if (typeBound is UserDefinedType { ResolvedClass: { } parentDecl }) {
          yield return parentDecl;
        }
      }
    }
  }

  public TypeParameter(IOrigin rangeOrigin, Name name, TPVarianceSyntax varianceS, TypeParameterCharacteristics characteristics,
    List<Type> typeBounds)
    : base(rangeOrigin, name, null, new List<TypeParameter>(), null, false) {
    Contract.Requires(rangeOrigin != null);
    Contract.Requires(name != null);
    Characteristics = characteristics;
    VarianceSyntax = varianceS;
    TypeBounds = typeBounds;
  }

  public TypeParameter(IOrigin rangeOrigin, Name name, TPVarianceSyntax varianceS)
    : this(rangeOrigin, name, varianceS, new TypeParameterCharacteristics(false), new List<Type>()) {
    Contract.Requires(rangeOrigin != null);
    Contract.Requires(name != null);
  }

  public TypeParameter(IOrigin tok, Name name, int positionalIndex, ParentType parent)
    : this(tok, name, TPVarianceSyntax.NonVariant_Strict) {
    PositionalIndex = positionalIndex;
    Parent = parent;
  }

  /// <summary>
  /// Return a list of unresolved clones of the type parameters in "typeParameters".
  /// </summary>
  public static List<TypeParameter> CloneTypeParameters(List<TypeParameter> typeParameters) {
    var cloner = new Cloner();
    return typeParameters.ConvertAll(tp => {
      var typeBounds = tp.TypeBounds.ConvertAll(cloner.CloneType);
      return new TypeParameter(tp.Origin, tp.NameNode, tp.VarianceSyntax, tp.Characteristics, typeBounds);
    });
  }

  public override string FullName {
    get {
      // when debugging, print it all:
      return /* Parent.FullName + "." + */ Name;
    }
  }

  public override SymbolKind? Kind => SymbolKind.TypeParameter;
  public override string GetDescription(DafnyOptions options) {
    return null; // TODO test the effect of this
  }

  public static TypeParameterCharacteristics GetExplicitCharacteristics(TopLevelDecl d) {
    Contract.Requires(d != null);
    TypeParameterCharacteristics characteristics = new TypeParameterCharacteristics(false);
    if (d is AbstractTypeDecl) {
      var dd = (AbstractTypeDecl)d;
      characteristics = dd.Characteristics;
    } else if (d is TypeSynonymDecl) {
      var dd = (TypeSynonymDecl)d;
      characteristics = dd.Characteristics;
    }
    if (characteristics.EqualitySupport == EqualitySupportValue.InferredRequired) {
      return new TypeParameterCharacteristics(EqualitySupportValue.Unspecified, characteristics.AutoInit, characteristics.ContainsNoReferenceTypes);
    } else {
      return characteristics;
    }
  }

  public static Dictionary<TypeParameter, Type> SubstitutionMap(List<TypeParameter> formals, List<Type> actuals) {
    Contract.Requires(formals != null);
    Contract.Requires(actuals != null);
    Contract.Requires(formals.Count == actuals.Count);
    var subst = new Dictionary<TypeParameter, Type>();
    for (int i = 0; i < formals.Count; i++) {
      subst.Add(formals[i], actuals[i]);
    }
    return subst;
  }

  public override List<Type> ParentTypes(List<Type> typeArgs, bool includeTypeBounds) {
    return includeTypeBounds ? TypeBounds : new List<Type>();
  }
}