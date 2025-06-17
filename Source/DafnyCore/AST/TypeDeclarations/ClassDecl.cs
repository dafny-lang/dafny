#nullable enable
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

  [SyntaxConstructor]
  public ClassDecl(IOrigin origin, Name nameNode, Attributes? attributes,
    List<TypeParameter> typeArgs, ModuleDefinition enclosingModuleDefinition,
    [Captured] List<MemberDecl> members, List<Type> traits, bool isRefining)
    : base(origin, nameNode, attributes, typeArgs, enclosingModuleDefinition, members, traits) {
    Contract.Requires(origin != null);
    Contract.Requires(nameNode != null);
    Contract.Requires(enclosingModuleDefinition != null);
    Contract.Requires(cce.NonNullElements(typeArgs));
    Contract.Requires(cce.NonNullElements(members));
    NonNullTypeDecl = new NonNullTypeDecl(this);
    IsRefining = isRefining;
    this.NewSelfSynonym();
  }
  public override bool IsRefining { get; }
}