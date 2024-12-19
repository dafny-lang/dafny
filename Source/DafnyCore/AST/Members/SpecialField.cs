using System.Collections.Generic;
using System.Diagnostics.Contracts;

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
  public readonly ID SpecialId;
  public readonly object IdParam;

  public SpecialField(IOrigin rangeOrigin, string name, ID specialId, object idParam,
    bool isGhost, bool isMutable, bool isUserMutable, Type type, Attributes attributes)
    : this(rangeOrigin, new Name(name), specialId, idParam, false, isGhost, isMutable, isUserMutable, type, attributes) {
  }

  public SpecialField(IOrigin rangeOrigin, Name name, ID specialId, object idParam,
    bool hasStaticKeyword, bool isGhost, bool isMutable, bool isUserMutable, Type type, Attributes attributes)
    : base(rangeOrigin, name, hasStaticKeyword, isGhost, isMutable, isUserMutable, type, attributes) {
    Contract.Requires(rangeOrigin != null);
    Contract.Requires(name != null);
    Contract.Requires(!isUserMutable || isMutable);
    Contract.Requires(type != null);

    SpecialId = specialId;
    IdParam = idParam;
  }

  public override string FullName {
    get {
      Contract.Ensures(Contract.Result<string>() != null);
      return EnclosingClass != null ? EnclosingClass.FullName + "." + Name : Name;
    }
  }

  public override string FullSanitizedName { // Override beacuse EnclosingClass may be null
    get {
      Contract.Ensures(Contract.Result<string>() != null);
      return EnclosingClass != null ? EnclosingClass.FullSanitizedName + "." + SanitizedName : SanitizedName;
    }
  }

  public override string GetCompileName(DafnyOptions options) {
    Contract.Ensures(Contract.Result<string>() != null);
    return EnclosingClass != null ? base.GetCompileName(options) : Name;
  }
}

public class DatatypeDiscriminator : SpecialField {
  public override string WhatKind {
    get { return "discriminator"; }
  }

  public DatatypeDiscriminator(IOrigin rangeOrigin, Name name, ID specialId, object idParam, bool isGhost, Type type, Attributes attributes)
    : base(rangeOrigin, name, specialId, idParam, false, isGhost, false, false, type, attributes) {
  }
}

public class DatatypeDestructor : SpecialField {
  public readonly List<DatatypeCtor> EnclosingCtors = new List<DatatypeCtor>();  // is always a nonempty list
  public readonly List<Formal> CorrespondingFormals = new List<Formal>();  // is always a nonempty list
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(EnclosingCtors != null);
    Contract.Invariant(CorrespondingFormals != null);
    Contract.Invariant(EnclosingCtors.Count > 0);
    Contract.Invariant(EnclosingCtors.Count == CorrespondingFormals.Count);
  }

  public DatatypeDestructor(IOrigin rangeOrigin, DatatypeCtor enclosingCtor, Formal correspondingFormal, Name name, string compiledName, bool isGhost, Type type, Attributes attributes)
    : base(rangeOrigin, name, SpecialField.ID.UseIdParam, compiledName, false, isGhost, false, false, type, attributes) {
    Contract.Requires(rangeOrigin != null);
    Contract.Requires(enclosingCtor != null);
    Contract.Requires(correspondingFormal != null);
    Contract.Requires(name != null);
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

  static internal string PrintableCtorNameList(List<DatatypeCtor> ctors, string grammaticalConjunction) {
    Contract.Requires(ctors != null);
    Contract.Requires(grammaticalConjunction != null);
    return Util.PrintableNameList(ctors.ConvertAll(ctor => ctor.Name), grammaticalConjunction);
  }
}