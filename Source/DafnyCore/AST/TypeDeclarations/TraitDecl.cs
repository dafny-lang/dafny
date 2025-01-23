using System.Collections.Generic;
using Microsoft.Dafny.Auditor;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public class TraitDecl : ClassLikeDecl {
  public override string WhatKind => "trait";
  public bool IsParent { set; get; }
  public override bool AcceptThis => true;

  [FilledInDuringResolution] public List<TraitDecl> TraitDeclsCanBeDowncastedTo = new();

  internal void SetUpAsReferenceType(bool isReferenceType) {
    // Note, it's important to set .NonNullTypeDecl first, before calling NewSelfSynonym(), since the latter will look at the former.
    Contract.Assert(NonNullTypeDecl == null); // SetUpAsReferenceType should be called only once
    if (isReferenceType) {
      NonNullTypeDecl = new NonNullTypeDecl(this);
    }

    this.NewSelfSynonym();
  }

  public override bool IsReferenceTypeDecl => NonNullTypeDecl != null;

  /// <summary>
  /// This constructor creates a TraitDecl object. However, before the object really functions as a TraitDecl, it is necessary
  /// to call SetUpAsReferenceType, which sets .NonNullTypeDecl (if necessary) and calls NewSelfSynonym().
  /// </summary>
  public TraitDecl(IOrigin origin, Name name, ModuleDefinition module,
    List<TypeParameter> typeArgs, [Captured] List<MemberDecl> members, Attributes attributes, bool isRefining, List<Type> /*?*/ traits)
    : base(origin, name, module, typeArgs, members, attributes, isRefining, traits) {
  }

  public override IEnumerable<Assumption> Assumptions(Declaration decl) {
    foreach (var assumption in base.Assumptions(this)) {
      yield return assumption;
    }

    if (Attributes.Find(Attributes, "termination") is { } ta &&
        ta.Args.Count == 1 && Expression.IsBoolLiteral(ta.Args[0], out var termCheck) &&
        termCheck == false) {
      yield return new Assumption(this, Origin, AssumptionDescription.HasTerminationFalseAttribute);
    }
  }

  // Given a trait declaration, returns the list of traits that this trait can downcast to,
  // using its type parameters only (no run-time information about the type available)
  // Used in backends that apply monomorphization
  public List<Type> DowncastableSubTraitsIfMonomorphized() {
    var downcastableTraits = new List<Type>();
    foreach (var subTrait in TraitDeclsCanBeDowncastedTo) {
      // Recovers which of the parent traits of the subTraits is the current trait declaration
      var parentTrait = subTrait.ParentTraits.FirstOrDefault(t => t.AsTraitType == this);
      Type downcastType = null;
      if (parentTrait is UserDefinedType { TypeArgs: var parentTypeArguments } &&
          CanDowncastIfMonomorphized(parentTypeArguments, subTrait, ref downcastType)) {
        downcastableTraits.Add(downcastType);
      }
    }

    return downcastableTraits;
  }

  /// When traits generics are monomorphized, i.e. they are simply instantiated for every type for which they are used,
  /// it becomes impossible to express some downcasts in the target language. For example,
  /// trait SuperTrait {}
  /// trait SubTrait<T> extends SuperTrait {}
  /// Although it's possible to cast a SubTrait<int> to a SuperTrait, the other direction is not possible
  /// if traits are monomorphized, because there could be infinitely new traits depending on the generic argument,
  /// and traits only build a finite virtual dispatch table.
  /// This algorithm determines if there are enough type parameters in common so that the downcast can be known
  /// no matter what 
  public bool CanDowncastIfMonomorphized(
    List<Type> parentTypeArguments, TraitDecl subTrait, ref Type downcastType) {
    // Algorithm:
    // trait Sub<TC1, ...TCn> extends Parent<PT1, ...PTn>   where trait Parent<TP1, ...TPn>
    // Foreach type parameter in the parent TPi
    //   if PTi is some TCj, store the mapping TCj => TPi. We need only to store the first of such mapping
    //   If PTi is anything else, ok
    // End of the loop: if not all children type parameters were found, cancel
    // build the type Sub<TP...> by iterating on the type parameters TC.
    Contract.Assert(TypeArgs.Count == parentTypeArguments.Count);
    var mapping = new Dictionary<TypeParameter, Type>();
    for (var i = 0; i < TypeArgs.Count; i++) {
      var TP = TypeArgs[i];
      var maybeTc = parentTypeArguments[i];
      if (maybeTc is UserDefinedType { ResolvedClass: TypeParameter maybeTc2 }) {
        if (subTrait.TypeArgs.Contains(maybeTc2) && !mapping.ContainsKey(maybeTc2)) {
          mapping.Add(maybeTc2, new UserDefinedType(TP));
        }
      }
    }

    var allTypeParametersCovered = subTrait.TypeArgs.TrueForAll(
      tp => mapping.ContainsKey(tp));
    if (allTypeParametersCovered) {
      // Now we need to make sure that type characteristics are compatible
      var typeArgs = subTrait.TypeArgs.Select(tp => mapping[tp]).ToList();
      for (var i = 0; i < typeArgs.Count; i++) {
        var downcastTypeParam = subTrait.TypeArgs[i];
        var parentType = typeArgs[i];
        if (!IsCompatibleWith(parentType, downcastTypeParam)) {
          return false;
        }
      }

      var subTraitTypeDowncastable =
        new UserDefinedType(Token.NoToken, subTrait.Name, subTrait, typeArgs);
      downcastType = subTraitTypeDowncastable;
      return true;
    }

    return false;
  }

  private static bool IsCompatibleWith(Type type, TypeParameter typeParameter) {
    return (typeParameter.Characteristics.EqualitySupport == TypeParameter.EqualitySupportValue.Unspecified ||
            type.SupportsEquality) && typeParameter.TypeBounds.TrueForAll(t => type.IsSubtypeOf(t, false, true));
  }
}