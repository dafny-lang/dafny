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

  public bool TryLookup(string name, out ModuleDecl m) {
    Contract.Requires(name != null);
    return TryLookupFilter(name, out m, l => true);
  }

  public bool TryLookupFilter(string name, out ModuleDecl m, Func<ModuleDecl, bool> filter) {
    Contract.Requires(name != null);
    if (modules.TryGetValue(name, out m) && filter(m)) {
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

  public bool ResolveQualifiedModuleIdRootAbstract(AbstractModuleDecl context, ModuleQualifiedId qid,
    out ModuleDecl result) {
    Contract.Assert(qid != null);
    IOrigin root = qid.Path[0].StartToken;
    result = null;
    bool res = TryLookupFilter(root.val, out result,
      m => context != m && ((context.EnclosingModuleDefinition == m.EnclosingModuleDefinition && context.Exports.Count == 0) || m is LiteralModuleDecl));
    return res;
  }

  /// <summary>
  /// Find a matching module for the root of the QualifiedId, ignoring
  /// (a) the module (context) itself and (b) any local imports
  /// The latter is so that if one writes 'import A`E  import F = A`F' the second A does not
  /// resolve to the alias produced by the first import
  /// </summary>
  public bool ResolveQualifiedModuleIdRootImport(AliasModuleDecl context, ModuleQualifiedId qid,
    out ModuleDecl result) {
    Contract.Assert(qid != null);
    IOrigin root = qid.Path[0].StartToken;
    result = null;
    bool res = TryLookupFilter(root.val, out result,
      m => context != m && ((context.EnclosingModuleDefinition == m.EnclosingModuleDefinition && context.Exports.Count == 0) || m is LiteralModuleDecl));
    return res;
  }

  public bool ResolveQualifiedModuleIdRootRefines(ModuleDefinition context, ModuleQualifiedId qid,
    out ModuleDecl result) {
    Contract.Assert(qid != null);
    IOrigin root = qid.Path[0].StartToken;
    result = null;
    bool res = TryLookupFilter(root.val, out result, m => m.EnclosingModuleDefinition != context);
    return res;
  }
}