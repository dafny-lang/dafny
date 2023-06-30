using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class ImplicitClassDecl : TopLevelDeclWithMembers, RevealableTypeDecl {
  public override string WhatKind => "top-level module declaration";
  public override bool AcceptThis => false;

  public TopLevelDecl AsTopLevelDecl => this;
  public TypeDeclSynonymInfo SynonymInfo { get; set; }

  public ImplicitClassDecl(ModuleDefinition module, MemberDecl member)
    : base(RangeToken.NoToken, new Name(GetName(member.Name)), module, new List<TypeParameter>(),
      new List<MemberDecl>() { member }, null, false, null) {
    Contract.Requires(module != null);
    this.NewSelfSynonym();
  }

  public static string GetName(string memberName) {
    return "_implicitClassFor" + memberName;
  }
}