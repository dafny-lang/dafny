using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public class DefaultClassDecl : TopLevelDeclWithMembers, RevealableTypeDecl {
  public override string WhatKind => "top-level module declaration";
  public override bool AcceptThis => false;

  public TopLevelDecl AsTopLevelDecl => this;
  public TypeDeclSynonymInfo SynonymInfo { get; set; }

  public DefaultClassDecl(ModuleDefinition module, [Captured] List<MemberDecl> members)
    : base(SourceOrigin.NoToken, new Name("_default"), module, new List<TypeParameter>(), members, null, false, null) {
    Contract.Requires(module != null);
    Contract.Requires(cce.NonNullElements(members));
    this.NewSelfSynonym();
  }
}