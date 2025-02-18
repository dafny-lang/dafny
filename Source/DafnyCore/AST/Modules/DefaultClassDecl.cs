#nullable enable
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
    List<TypeParameter> typeArgs, ModuleDefinition enclosingModule, 
    List<MemberDecl> members, List<Type> traits = null) 
    : base(origin, nameNode, attributes, typeArgs, enclosingModule, members, traits)
  {
  }

  public DefaultClassDecl(ModuleDefinition enclosingModule, [Captured] List<MemberDecl> members)
    : base(SourceOrigin.NoToken, new Name("_default"), null, [], enclosingModule, members) {
    Contract.Requires(enclosingModule != null);
    Contract.Requires(cce.NonNullElements(members));
    this.NewSelfSynonym();
  }
}