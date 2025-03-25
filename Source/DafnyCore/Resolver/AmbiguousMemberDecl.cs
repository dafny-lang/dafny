using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;

namespace Microsoft.Dafny;

class AmbiguousMemberDecl : MemberDecl, IAmbiguousThing<MemberDecl> // only used with "classes"
{
  public static MemberDecl Create(ModuleDefinition m, MemberDecl a, MemberDecl b) {
    ISet<MemberDecl> s;
    var t = AmbiguousThingHelper<MemberDecl>.Create(m, a, b, new Eq(), out s);
    return t ?? new AmbiguousMemberDecl(m, AmbiguousThingHelper<MemberDecl>.Name(s, member => member.Name), s);
  }

  class Eq : IEqualityComparer<MemberDecl> {
    public bool Equals(MemberDecl d0, MemberDecl d1) {
      return d0 == d1;
    }

    public int GetHashCode(MemberDecl d) {
      return d.GetHashCode();
    }
  }

  public override string WhatKind {
    get { return pool.First().WhatKind; }
  }

  public override bool HasStaticKeyword => true;

  public override SymbolKind? Kind => null;
  public override string GetDescription(DafnyOptions options) {
    return null;
  }

  readonly ISet<MemberDecl> pool;

  ISet<MemberDecl> IAmbiguousThing<MemberDecl>.Pool => pool;

  private AmbiguousMemberDecl(ModuleDefinition m, string name, ISet<MemberDecl> pool)
    : base(pool.First().Origin, new Name(pool.First().Origin, name), pool.First().IsGhost, null) {
    Contract.Requires(name != null);
    Contract.Requires(pool != null && 2 <= pool.Count);
    this.pool = pool;
  }

  public string ModuleNames() {
    return AmbiguousThingHelper<MemberDecl>.ModuleNames(this, d => d.EnclosingClass.EnclosingModuleDefinition.Name);
  }
}