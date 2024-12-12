using System.Collections.Generic;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny;

public class TypeSynonymDecl : TypeSynonymDeclBase, RevealableTypeDecl {
  public override string WhatKind => "type synonym";

  public TypeSynonymDecl(IOrigin rangeOrigin, Name name, TypeParameter.TypeParameterCharacteristics characteristics, List<TypeParameter> typeArgs, ModuleDefinition module, Type rhs, Attributes attributes)
    : base(rangeOrigin, name, characteristics, typeArgs, module, rhs, attributes) {
    this.NewSelfSynonym();
  }
  public TopLevelDecl AsTopLevelDecl => this;
  public TypeDeclSynonymInfo SynonymInfo { get; set; }
  public override SymbolKind? Kind => SymbolKind.Class;
  public override string GetDescription(DafnyOptions options) {
    return "type synonym";
  }
}

public class InternalTypeSynonymDecl : TypeSynonymDeclBase {
  public override string WhatKind { get { return "export-provided type"; } }
  public InternalTypeSynonymDecl(IOrigin rangeOrigin, Name name, TypeParameter.TypeParameterCharacteristics characteristics, List<TypeParameter> typeArgs, ModuleDefinition module, Type rhs, Attributes attributes)
    : base(rangeOrigin, name, characteristics, typeArgs, module, rhs, attributes) {
  }

  public override SymbolKind? Kind => SymbolKind.Class;
  public override string GetDescription(DafnyOptions options) {
    return "type synonym";
  }
}