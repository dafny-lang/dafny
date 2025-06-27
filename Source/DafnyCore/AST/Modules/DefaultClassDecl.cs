#nullable enable
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public class DefaultClassDecl : TopLevelDeclWithMembers, RevealableTypeDecl {
  public override string WhatKind => "top-level module declaration";
  public override bool AcceptThis => false;

  public TopLevelDecl AsTopLevelDecl => this;
  public TypeDeclSynonymInfo? SynonymInfo { get; set; }


  [SyntaxConstructor]
  public DefaultClassDecl(IOrigin origin, Name nameNode, Attributes? attributes,
    List<TypeParameter> typeArgs, ModuleDefinition enclosingModuleDefinition,
    List<MemberDecl> members, List<Type> traits)
    : base(origin, nameNode, enclosingModuleDefinition, typeArgs, members, attributes, traits) {
  }

  public DefaultClassDecl(ModuleDefinition enclosingModule, [Captured] List<MemberDecl> members)
    : base(SourceOrigin.NoToken, new Name("_default"), enclosingModule, [], members, null, []) {
    Contract.Requires(enclosingModule != null);
    Contract.Requires(Cce.NonNullElements(members));
    this.NewSelfSynonym();
  }
}