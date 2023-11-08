using System.Collections.Generic;

namespace Microsoft.Dafny;

public class TypeSynonymDecl : TypeSynonymDeclBase, RevealableTypeDecl {
  public override string WhatKind => "type synonym";

  public TypeSynonymDecl(RangeToken rangeToken, Name name, TypeParameter.TypeParameterCharacteristics characteristics, List<TypeParameter> typeArgs, ModuleDefinition module, Type rhs, Attributes attributes)
    : base(rangeToken, name, characteristics, typeArgs, module, rhs, attributes) {
    this.NewSelfSynonym();
  }
  public TopLevelDecl AsTopLevelDecl => this;
  public TypeDeclSynonymInfo SynonymInfo { get; set; }
  public override DafnySymbolKind Kind => DafnySymbolKind.Class;
  public override string GetDescription(DafnyOptions options) {
    return "type synonym";
  }
}

public class InternalTypeSynonymDecl : TypeSynonymDeclBase {
  public override string WhatKind { get { return "export-provided type"; } }
  public InternalTypeSynonymDecl(RangeToken rangeToken, Name name, TypeParameter.TypeParameterCharacteristics characteristics, List<TypeParameter> typeArgs, ModuleDefinition module, Type rhs, Attributes attributes)
    : base(rangeToken, name, characteristics, typeArgs, module, rhs, attributes) {
  }

  public override DafnySymbolKind Kind => DafnySymbolKind.Class;
  public override string GetDescription(DafnyOptions options) {
    return "type synonym";
  }
}