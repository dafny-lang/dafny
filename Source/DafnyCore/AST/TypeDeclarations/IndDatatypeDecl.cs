using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public class IndDatatypeDecl : DatatypeDecl, ITentativeEqualitySupportingDeclaration {
  public override string WhatKind { get { return "datatype"; } }
  [FilledInDuringResolution] public DatatypeCtor GroundingCtor; // set during resolution (possibly to null)

  public override DatatypeCtor GetGroundingCtor() {
    return GroundingCtor ?? Ctors.FirstOrDefault(ctor => ctor.IsGhost, Ctors[0]);
  }

  private bool[] typeParametersUsedInConstructionByGroundingCtor;

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

  public ITentativeEqualitySupportingDeclaration.ES EqualitySupport { get; set; } = ITentativeEqualitySupportingDeclaration.ES.NotYetComputed;

  List<TypeParameter> ITentativeEqualitySupportingDeclaration.TypeParameters {
    get => TypeArgs;
  }

  ModuleDefinition ITentativeEqualitySupportingDeclaration.EnclosingModuleDefinition =>
    EnclosingModuleDefinition;

  public IndDatatypeDecl(RangeToken rangeOrigin, Name name, ModuleDefinition module, List<TypeParameter> typeArgs,
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

  public override bool AcceptThis => true;
}