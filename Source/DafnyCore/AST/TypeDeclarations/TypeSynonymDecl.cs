using System.Collections.Generic;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny;

class ConcreteTypeSynonymDecl : TypeSynonymDecl {
  public ConcreteTypeSynonymDecl(IOrigin origin, Name nameNode, TypeParameterCharacteristics characteristics,
    List<TypeParameter> typeArgs, ModuleDefinition enclosingModuleDefinition,
    Type rhs, Attributes attributes)
      : base(origin, nameNode, characteristics, typeArgs, enclosingModuleDefinition, attributes) {
    Rhs = rhs;
  }

  public override Type Rhs { get; }
}

public abstract class TypeSynonymDecl : TypeSynonymDeclBase, RevealableTypeDecl {
  public override string WhatKind => "type synonym";

  [SyntaxConstructor]
  protected TypeSynonymDecl(IOrigin origin, Name nameNode, TypeParameterCharacteristics characteristics,
    List<TypeParameter> typeArgs, ModuleDefinition enclosingModuleDefinition, Attributes attributes)
    : base(origin, nameNode, characteristics, typeArgs, enclosingModuleDefinition, attributes) {
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
  public InternalTypeSynonymDecl(IOrigin origin, Name name, TypeParameterCharacteristics characteristics, List<TypeParameter> typeArgs, ModuleDefinition module, Type rhs, Attributes attributes)
    : base(origin, name, characteristics, typeArgs, module, attributes) {
    Rhs = rhs;
  }

  public override Type Rhs { get; }

  public override SymbolKind? Kind => SymbolKind.Class;
  public override string GetDescription(DafnyOptions options) {
    return "type synonym";
  }
}