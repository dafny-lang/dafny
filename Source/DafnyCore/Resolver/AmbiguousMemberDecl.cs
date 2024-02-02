using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

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
    get { return Pool.First().WhatKind; }
  }

  readonly ISet<MemberDecl> Pool = new HashSet<MemberDecl>();

  ISet<MemberDecl> IAmbiguousThing<MemberDecl>.Pool {
    get { return Pool; }
  }

  private AmbiguousMemberDecl(ModuleDefinition m, string name, ISet<MemberDecl> pool)
    : base(pool.First().RangeToken, new Name(pool.First().RangeToken, name), true, pool.First().IsGhost, null, false) {
    Contract.Requires(name != null);
    Contract.Requires(pool != null && 2 <= pool.Count);
    Pool = pool;
  }

  public string ModuleNames() {
    return AmbiguousThingHelper<MemberDecl>.ModuleNames(this, d => d.EnclosingClass.EnclosingModuleDefinition.Name);
  }
}