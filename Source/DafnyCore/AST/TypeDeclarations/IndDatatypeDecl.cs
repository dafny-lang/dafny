#nullable enable
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public class IndDatatypeDecl : DatatypeDecl {
  public override string WhatKind { get { return "datatype"; } }
  [FilledInDuringResolution] public DatatypeCtor? GroundingCtor; // set during resolution (possibly to null)

  public override DatatypeCtor GetGroundingCtor() {
    return GroundingCtor ?? Ctors.FirstOrDefault(ctor => ctor.IsGhost, Ctors[0]);
  }

  private bool[]? typeParametersUsedInConstructionByGroundingCtor;

  public bool[] TypeParametersUsedInConstructionByGroundingCtor {
    get {
      if (typeParametersUsedInConstructionByGroundingCtor == null) {
        typeParametersUsedInConstructionByGroundingCtor = new bool[TypeArgs.Count];
        for (var i = 0; i < typeParametersUsedInConstructionByGroundingCtor.Length; i++) {
          typeParametersUsedInConstructionByGroundingCtor[i] = true;
        }
      }
      return typeParametersUsedInConstructionByGroundingCtor;
    }
    set {
      typeParametersUsedInConstructionByGroundingCtor = value;
    }
  }

  public enum ES { NotYetComputed, Never, ConsultTypeArguments }
  public ES EqualitySupport = ES.NotYetComputed;

  [SyntaxConstructor]
  public IndDatatypeDecl(IOrigin origin, Name nameNode, ModuleDefinition enclosingModuleDefinition, List<TypeParameter> typeArgs,
    [Captured] List<DatatypeCtor> ctors, List<Type> traits, List<MemberDecl> members, Attributes? attributes, bool isRefining)
    : base(origin, nameNode, enclosingModuleDefinition, typeArgs, ctors, traits, members, attributes, isRefining) {
    Contract.Requires(origin != null);
    Contract.Requires(nameNode != null);
    Contract.Requires(enclosingModuleDefinition != null);
    Contract.Requires(Cce.NonNullElements(typeArgs));
    Contract.Requires(Cce.NonNullElements(ctors));
    Contract.Requires(Cce.NonNullElements(members));
    Contract.Requires((isRefining && ctors.Count == 0) || (!isRefining && 1 <= ctors.Count));
  }

  public override bool AcceptThis => true;
}