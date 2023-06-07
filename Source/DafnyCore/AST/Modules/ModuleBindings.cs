using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class ModuleBindings {
  private ModuleBindings parent;
  private Dictionary<string, ModuleDecl> modules;
  private Dictionary<string, ModuleBindings> bindings;

  public ModuleBindings(ModuleBindings p) {
    parent = p;
    modules = new Dictionary<string, ModuleDecl>();
    bindings = new Dictionary<string, ModuleBindings>();
  }

  public bool BindName(string name, ModuleDecl subModule, ModuleBindings b) {
    if (modules.ContainsKey(name)) {
      return false;
    } else {
      modules.Add(name, subModule);
      bindings.Add(name, b);
      return true;
    }
  }

  public bool TryLookup(IToken name, out ModuleDecl m) {
    Contract.Requires(name != null);
    return TryLookupFilter(name, out m, l => true);
  }

  public bool TryLookupFilter(IToken name, out ModuleDecl m, Func<ModuleDecl, bool> filter) {
    Contract.Requires(name != null);
    if (modules.TryGetValue(name.val, out m) && filter(m)) {
      return true;
    } else if (parent != null) {
      return parent.TryLookupFilter(name, out m, filter);
    } else {
      return false;
    }
  }

  public IEnumerable<ModuleDecl> ModuleList {
    get { return modules.Values; }
  }

  public ModuleBindings SubBindings(string name) {
    ModuleBindings v = null;
    bindings.TryGetValue(name, out v);
    return v;
  }
}