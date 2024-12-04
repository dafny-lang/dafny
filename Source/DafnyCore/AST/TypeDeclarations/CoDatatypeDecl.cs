using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public class CoDatatypeDecl : DatatypeDecl {
  public override string WhatKind { get { return "codatatype"; } }
  [FilledInDuringResolution] public CoDatatypeDecl SscRepr;

  public CoDatatypeDecl(IOrigin rangeOrigin, Name name, ModuleDefinition module, List<TypeParameter> typeArgs,
    [Captured] List<DatatypeCtor> ctors, List<Type> parentTraits, List<MemberDecl> members, Attributes attributes, bool isRefining)
    : base(rangeOrigin, name, module, typeArgs, ctors, parentTraits, members, attributes, isRefining) {
    Contract.Requires(rangeOrigin != null);
    Contract.Requires(name != null);
    Contract.Requires(module != null);
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