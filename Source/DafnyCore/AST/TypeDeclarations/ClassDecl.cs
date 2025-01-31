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
    Contract.Invariant(Traits != null);
  }

  public ClassDecl(IOrigin origin, Name name, ModuleDefinition enclosingModule,
    List<TypeParameter> typeArgs, [Captured] List<MemberDecl> members, Attributes attributes, bool isRefining, List<Type>/*?*/ traits)
    : base(origin, name, enclosingModule, typeArgs, members, attributes, traits) {
    Contract.Requires(origin != null);
    Contract.Requires(name != null);
    Contract.Requires(enclosingModule != null);
    Contract.Requires(cce.NonNullElements(typeArgs));
    Contract.Requires(cce.NonNullElements(members));
    NonNullTypeDecl = new NonNullTypeDecl(this);
    IsRefining = isRefining;
    this.NewSelfSynonym();
  }

  public override bool IsRefining { get; }
}