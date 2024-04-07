using System;
using System.Collections.Generic;

namespace Microsoft.Dafny;

public abstract class OrderedModuleDecl : ModuleDecl {
  internal HashSet<ModuleQualifiedId> Above;
  internal HashSet<ModuleQualifiedId> Below;
  
  public OrderedModuleDecl(Cloner cloner, OrderedModuleDecl original, ModuleDefinition parent)
    : base(cloner, original, parent) {
    Above = original.Above;
    Below = original.Below;
  }

  public OrderedModuleDecl(DafnyOptions options, RangeToken rangeToken, Name name,
    ModuleDefinition parent, bool opened, Guid cloneId)
    : base(options, rangeToken, name, parent, opened, false, cloneId) {
    Above = new HashSet<ModuleQualifiedId>();
    Below = new HashSet<ModuleQualifiedId>();
  }

  public void Add(IEnumerable<ModuleQualifiedId> s, bool above = true) {
    (above ? Above : Below).UnionWith(s);
  }
  
}