using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public class CoDatatypeDecl : DatatypeDecl {
  public override string WhatKind { get { return "codatatype"; } }
  [FilledInDuringResolution] public CoDatatypeDecl SscRepr;

  public CoDatatypeDecl(IOrigin origin, Name nameNode, ModuleDefinition enclosingModule, List<TypeParameter> typeArgs,
    [Captured] List<DatatypeCtor> ctors, List<Type> traits, List<MemberDecl> members, Attributes attributes, bool isRefining)
    : base(origin, nameNode, enclosingModule, typeArgs, ctors, traits, members, attributes, isRefining) {
    Contract.Requires(origin != null);
    Contract.Requires(nameNode != null);
    Contract.Requires(enclosingModule != null);
    Contract.Requires(cce.NonNullElements(typeArgs));
    Contract.Requires(cce.NonNullElements(ctors));
    Contract.Requires(cce.NonNullElements(members));
    Contract.Requires((isRefining && ctors.Count == 0) || (!isRefining && 1 <= ctors.Count));
  }

  public override DatatypeCtor GetGroundingCtor() {
    return Ctors.FirstOrDefault(ctor => ctor.IsGhost, Ctors[0]);
  }

  public override bool AcceptThis => true;
}