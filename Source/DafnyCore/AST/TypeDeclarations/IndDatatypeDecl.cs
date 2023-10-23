using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class IndDatatypeDecl : DatatypeDecl {
  public override string WhatKind { get { return "datatype"; } }
  public DatatypeCtor GroundingCtor;  // set during resolution

  public override DatatypeCtor GetGroundingCtor() {
    return GroundingCtor;
  }

  public bool[] TypeParametersUsedInConstructionByGroundingCtor;  // set during resolution; has same length as the number of type arguments

  public enum ES { NotYetComputed, Never, ConsultTypeArguments }
  public ES EqualitySupport = ES.NotYetComputed;

  public IndDatatypeDecl(RangeToken rangeToken, Name name, ModuleDefinition module, List<TypeParameter> typeArgs,
    [Captured] List<DatatypeCtor> ctors, List<Type> parentTraits, List<MemberDecl> members, Attributes attributes, bool isRefining)
    : base(rangeToken, name, module, typeArgs, ctors, parentTraits, members, attributes, isRefining) {
    Contract.Requires(rangeToken != null);
    Contract.Requires(name != null);
    Contract.Requires(module != null);
    Contract.Requires(cce.NonNullElements(typeArgs));
    Contract.Requires(cce.NonNullElements(ctors));
    Contract.Requires(cce.NonNullElements(members));
    Contract.Requires((isRefining && ctors.Count == 0) || (!isRefining && 1 <= ctors.Count));
  }

  public override bool AcceptThis => true;
}