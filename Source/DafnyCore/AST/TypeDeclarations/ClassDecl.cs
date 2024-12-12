using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class ClassDecl : ClassLikeDecl {
  public override string WhatKind => "class";
  public override bool IsReferenceTypeDecl => true;
  public override bool AcceptThis => true;

  [FilledInDuringResolution] public bool HasConstructor;  // filled in (early) during resolution; true iff there exists a member that is a Constructor
  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(cce.NonNullElements(Members));
    Contract.Invariant(ParentTraits != null);
  }

  public ClassDecl(IOrigin rangeOrigin, Name name, ModuleDefinition module,
    List<TypeParameter> typeArgs, [Captured] List<MemberDecl> members, Attributes attributes, bool isRefining, List<Type>/*?*/ traits)
    : base(rangeOrigin, name, module, typeArgs, members, attributes, isRefining, traits) {
    Contract.Requires(rangeOrigin != null);
    Contract.Requires(name != null);
    Contract.Requires(module != null);
    Contract.Requires(cce.NonNullElements(typeArgs));
    Contract.Requires(cce.NonNullElements(members));
    NonNullTypeDecl = new NonNullTypeDecl(this);
    this.NewSelfSynonym();
  }
}