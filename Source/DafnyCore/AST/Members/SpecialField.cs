using System.Collections.Generic;
using System.Diagnostics.Contracts;
using JetBrains.Annotations;

namespace Microsoft.Dafny;

public class SpecialField : Field {
  public enum ID {
    UseIdParam,  // IdParam is a string
    ArrayLength,  // IdParam is null for .Length; IdParam is an int "x" for GetLength(x)
    ArrayLengthInt,  // same as ArrayLength, but produces int instead of BigInteger
    Floor,
    IsLimit,
    IsSucc,
    Offset,
    IsNat,
    Keys,
    Values,
    Items,
    Reads,
    Modifies,
    New,
  }
  public ID SpecialId;
  public object IdParam;

  public SpecialField(Cloner cloner, SpecialField original) : base(cloner, original) {
    IsMutable = original.IsMutable;
    IsUserMutable = original.IsUserMutable;
    SpecialId = original.SpecialId;
    IdParam = original.IdParam;
  }

  public SpecialField(IOrigin origin, string name, ID specialId, object idParam,
    bool isGhost, bool isMutable, bool isUserMutable, Type explicitType, Attributes attributes)
    : this(origin, new Name(origin, name), specialId, idParam, isGhost, isMutable, isUserMutable, explicitType, attributes) {
  }

  public SpecialField(IOrigin origin, Name nameNode, ID specialId, object idParam,
    bool isGhost, bool isMutable, bool isUserMutable, Type explicitType, Attributes attributes)
    : base(origin, nameNode, isGhost, explicitType, attributes) {
    Contract.Requires(origin != null);
    Contract.Requires(nameNode != null);
    Contract.Requires(!isUserMutable || isMutable);

    IsMutable = isMutable;
    IsUserMutable = isUserMutable;
    SpecialId = specialId;
    IdParam = idParam;
  }

  public override bool IsMutable { get; }
  public override bool IsUserMutable { get; }

  public override string FullName {
    get {
      Contract.Ensures(Contract.Result<string>() != null);
      return EnclosingClass != null ? EnclosingClass.FullName + "." + Name : Name;
    }
  }

  public override string FullSanitizedName { // Override because EnclosingClass may be null
    get {
      Contract.Ensures(Contract.Result<string>() != null);
      return EnclosingMethod != null ? EnclosingMethod.FullSanitizedName + "." + SanitizedName
        : EnclosingClass != null ? EnclosingClass.FullSanitizedName + "." + SanitizedName : SanitizedName;
    }
  }

  // Used by referrers to designate the memory location of local variables and method parameters
  [FilledInDuringResolution]
  [CanBeNull] public MethodOrConstructor EnclosingMethod { get; set; }

  public override string GetCompileName(DafnyOptions options) {
    Contract.Ensures(Contract.Result<string>() != null);
    return EnclosingClass != null ? base.GetCompileName(options) : Name;
  }
}

public class DatatypeDiscriminator : SpecialField {
  public override string WhatKind {
    get { return "discriminator"; }
  }

  public DatatypeDiscriminator(IOrigin origin, Name nameNode, ID specialId, object idParam, bool isGhost, Type type, Attributes attributes)
    : base(origin, nameNode, specialId, idParam, isGhost, false, false, type, attributes) {
  }
}

public class DatatypeDestructor : SpecialField {
  public List<DatatypeCtor> EnclosingCtors = [];  // is always a nonempty list
  public List<Formal> CorrespondingFormals = [];  // is always a nonempty list
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(EnclosingCtors != null);
    Contract.Invariant(CorrespondingFormals != null);
    Contract.Invariant(EnclosingCtors.Count > 0);
    Contract.Invariant(EnclosingCtors.Count == CorrespondingFormals.Count);
  }

  public DatatypeDestructor(IOrigin origin, DatatypeCtor enclosingCtor, Formal correspondingFormal, Name nameNode, string compiledName, bool isGhost, Type type, Attributes attributes)
    : base(origin, nameNode, SpecialField.ID.UseIdParam, compiledName, isGhost, false, false, type, attributes) {
    Contract.Requires(origin != null);
    Contract.Requires(enclosingCtor != null);
    Contract.Requires(correspondingFormal != null);
    Contract.Requires(nameNode != null);
    Contract.Requires(type != null);
    EnclosingCtors.Add(enclosingCtor);  // more enclosing constructors may be added later during resolution
    CorrespondingFormals.Add(correspondingFormal);  // more corresponding formals may be added later during resolution
  }

  /// <summary>
  /// To be called only by the resolver. Called to share this datatype destructor between multiple constructors
  /// of the same datatype.
  /// </summary>
  internal void AddAnotherEnclosingCtor(DatatypeCtor ctor, Formal formal) {
    Contract.Requires(ctor != null);
    Contract.Requires(formal != null);
    EnclosingCtors.Add(ctor);  // more enclosing constructors may be added later during resolution
    CorrespondingFormals.Add(formal);  // more corresponding formals may be added later during resolution
  }

  internal string EnclosingCtorNames(string grammaticalConjunction) {
    Contract.Requires(grammaticalConjunction != null);
    return PrintableCtorNameList(EnclosingCtors, grammaticalConjunction);
  }

  internal static string PrintableCtorNameList(List<DatatypeCtor> ctors, string grammaticalConjunction) {
    Contract.Requires(ctors != null);
    Contract.Requires(grammaticalConjunction != null);
    return Util.PrintableNameList(ctors.ConvertAll(ctor => ctor.Name), grammaticalConjunction);
  }
}