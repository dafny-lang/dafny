using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public class DefaultClassDecl : TopLevelDeclWithMembers, RevealableTypeDecl {
  public override string WhatKind => "top-level module declaration";
  public override bool AcceptThis => false;

  public TopLevelDecl AsTopLevelDecl => this;
  public TypeDeclSynonymInfo SynonymInfo { get; set; }

  [ParseConstructor]
  public DefaultClassDecl(IOrigin origin, Name nameNode, Attributes? attributes,
    List<TypeParameter> typeArgs, ModuleDefinition enclosingModuleDefinition,
    List<MemberDecl> members, List<Type> traits = null)
    : base(origin, nameNode, enclosingModuleDefinition, typeArgs, members, attributes, traits) {
  }
  
  public DefaultClassDecl(ModuleDefinition module, [Captured] List<MemberDecl> members)
    : base(SourceOrigin.NoToken, new Name("_default"), module, [], members, null, null) {
    Contract.Requires(module != null);
    Contract.Requires(cce.NonNullElements(members));
    this.NewSelfSynonym();
  }
}