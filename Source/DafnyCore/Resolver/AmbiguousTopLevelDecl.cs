using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

namespace Microsoft.Dafny;

public class AmbiguousTopLevelDecl : TopLevelDecl, IAmbiguousThing<TopLevelDecl> // only used with "classes"
{
  public static TopLevelDecl Create(ModuleDefinition m, TopLevelDecl a, TopLevelDecl b) {
    var t = AmbiguousThingHelper<TopLevelDecl>.Create(m, a, b, new Eq(), out var s);
    return t ?? new AmbiguousTopLevelDecl(m, AmbiguousThingHelper<TopLevelDecl>.Name(s, tld => tld.Name), s);
  }

  class Eq : IEqualityComparer<TopLevelDecl> {
    public bool Equals(TopLevelDecl d0, TopLevelDecl d1) {
      // We'd like to resolve any AliasModuleDecl to whatever module they refer to.
      // It seems that the only way to do that is to look at alias.Signature.ModuleDef,
      // but that is a ModuleDefinition, which is not a TopLevelDecl.  Therefore, we
      // convert to a ModuleDefinition anything that might refer to something that an
      // AliasModuleDecl can refer to; this is AliasModuleDecl and LiteralModuleDecl.
      object a = d0 is ModuleDecl ? ((ModuleDecl)d0).Dereference() : d0;
      object b = d1 is ModuleDecl ? ((ModuleDecl)d1).Dereference() : d1;
      return a == b;
    }

    public int GetHashCode(TopLevelDecl d) {
      object a = d is ModuleDecl ? ((ModuleDecl)d).Dereference() : d;
      return a.GetHashCode();
    }
  }

  public override string WhatKind {
    get { return Pool.First().WhatKind; }
  }

  readonly ISet<TopLevelDecl> Pool = new HashSet<TopLevelDecl>();

  ISet<TopLevelDecl> IAmbiguousThing<TopLevelDecl>.Pool {
    get { return Pool; }
  }

  private AmbiguousTopLevelDecl(ModuleDefinition m, string name, ISet<TopLevelDecl> pool)
    : base(pool.First().RangeToken, new Name(pool.First().RangeToken, name), m, new List<TypeParameter>(), null, false) {
    Contract.Requires(name != null);
    Contract.Requires(pool != null && 2 <= pool.Count);
    Pool = pool;
  }

  public string ModuleNames() {
    return AmbiguousThingHelper<TopLevelDecl>.ModuleNames(this, d => d.EnclosingModuleDefinition.Name);
  }
}