using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class ImplicitClassDecl : TopLevelDeclWithMembers, RevealableTypeDecl {
  public int Index { get; }
  public override string WhatKind => "top-level module declaration";
  public override string FullDafnyName => EnclosingModuleDefinition.FullDafnyName;
  public override bool AcceptThis => false;

  public TopLevelDecl AsTopLevelDecl => this;
  public TypeDeclSynonymInfo SynonymInfo { get; set; }

  public ImplicitClassDecl(ModuleDefinition module, MemberDecl member)
    : base(member.RangeToken, new Name(GetName(member.Name)), module, new List<TypeParameter>(),
      new List<MemberDecl>() { member }, null, false, null) {
    Contract.Requires(module != null);
    this.NewSelfSynonym();
  }

  public static string GetName(string memberName) {
    return memberName;
  }
}