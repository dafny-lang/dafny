using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Threading;

namespace Microsoft.Dafny; 

public class ProgramResolver {
  public Program Program { get; }

  public DafnyOptions Options { get; }
  public BuiltIns BuiltIns => Program.BuiltIns;
  public ErrorReporter Reporter { get; }

  public IList<IRewriter> rewriters;

  protected readonly Graph<ModuleDecl> dependencies = new();

  public FreshIdGenerator defaultTempVarIdGenerator = new();
  public readonly Dictionary<TopLevelDeclWithMembers, Dictionary<string, MemberDecl>> classMembers = new();

  public ProgramResolver(Program program) {
    this.Program = program;
    Reporter = program.Reporter;
    Options = program.Options;
  }

  public ValuetypeDecl AsValuetypeDecl(Type t) {
    Contract.Requires(t != null);
    foreach (var vtd in BuiltIns.valuetypeDecls) {
      if (vtd.IsThisType(t)) {
        return vtd;
      }
    }
    return null;
  }

  private static void ResolveValueTypeDecls(ProgramResolver programResolver) {
    var moduleResolver = new Resolver(programResolver);
    moduleResolver.moduleInfo = programResolver.BuiltIns.systemNameInfo;
    foreach (var valueTypeDecl in programResolver.BuiltIns.valuetypeDecls) {
      foreach (var member in valueTypeDecl.Members) {
        if (member is Function function) {
          moduleResolver.ResolveFunctionSignature(function);
          CallGraphBuilder.VisitFunction(function, programResolver.Reporter);
        } else if (member is Method method) {
          moduleResolver.ResolveMethodSignature(method);
          CallGraphBuilder.VisitMethod(method, programResolver.Reporter);
        }
      }
    }
  }


  public void Resolve(Program program, CancellationToken cancellationToken) {
    Contract.Requires(program != null);
    Type.ResetScopes();

    Type.EnableScopes();
    // For the formatter, we ensure we take snapshots of the PrefixNamedModules
    // and topleveldecls
    program.DefaultModuleDef.PreResolveSnapshotForFormatter();
    var origErrorCount = Reporter.ErrorCount; //TODO: This is used further below, but not in the >0 comparisons in the next few lines. Is that right?
    var bindings = new ModuleBindings(null);
    var bindings2 = program.DefaultModuleDef.BindModuleNames(this, bindings);
    bindings.BindName(program.DefaultModule.Name, program.DefaultModule, bindings2);

    if (Reporter.ErrorCount > 0) {
      return;
    } // if there were errors, then the implict ModuleBindings data structure invariant
      // is violated, so Processing dependencies will not succeed.

    // TODO: If we merge ProcessDependencies and resolving individual modules, then we don't need these pointers.
    // Or we need to change when ModuleQualifiedId.Root is set. We could update ModuleBindings when resolving ModuleDecls.
    Dictionary<ModuleDecl, Action<ModuleDecl>> declarationPointers = new();

    // Default module is never cached so this is a noop

    declarationPointers[program.DefaultModule] = v => program.DefaultModule = (LiteralModuleDecl)v;
    ProcessDependencies(program.DefaultModule, bindings2, dependencies, declarationPointers);
    // check for cycles in the import graph
    foreach (var cycle in dependencies.AllCycles()) {
      Resolver.ReportCycleError(Reporter, cycle, m => m.tok,
        m => (m is AliasModuleDecl ? "import " : "module ") + m.Name,
        "module definition contains a cycle (note: parent modules implicitly depend on submodules)");
    }

    if (Reporter.ErrorCount > 0) {
      return;
    }

    var sortedDecls = dependencies.TopologicallySortedComponents();
    program.ModuleSigs = new();

    SetHeights(sortedDecls);

    program.Compilation.Rewriters = Rewriters.GetRewriters(program, defaultTempVarIdGenerator);
    rewriters = program.Compilation.Rewriters;

    var systemClassMembers = ResolveBuiltins(program);
    foreach (var moduleClassMembers in systemClassMembers) {
      classMembers[moduleClassMembers.Key] = moduleClassMembers.Value;
    }

    foreach (var rewriter in rewriters) {
      cancellationToken.ThrowIfCancellationRequested();
      rewriter.PreResolve(program);
    }

    foreach (var decl in sortedDecls) {
      cancellationToken.ThrowIfCancellationRequested();
      var moduleResolutionResult = ResolveModuleDeclaration(program.Compilation, decl);
      declarationPointers[decl](moduleResolutionResult.ResolvedDeclaration);

      foreach (var sig in moduleResolutionResult.Signatures) {
        program.ModuleSigs[sig.Key] = sig.Value;
      }
      foreach (var moduleClassMembers in moduleResolutionResult.ClassMembers) {
        classMembers[moduleClassMembers.Key] = moduleClassMembers.Value;
      }

      foreach (var diagnostic in moduleResolutionResult.ErrorReporter.AllMessages) {
        Reporter.Message(diagnostic.Source, diagnostic.Level, diagnostic.ErrorId, diagnostic.Token,
          diagnostic.Message);
      }
    }

    if (Reporter.ErrorCount != origErrorCount) {
      return;
    }

    Type.DisableScopes();
    CheckDupModuleNames(program);

    foreach (var module in program.Modules()) { // TODO move this inside cached module resolution?
      foreach (var rewriter in rewriters) {
        cancellationToken.ThrowIfCancellationRequested();
        rewriter.PostResolve(module);
      }
    }

    foreach (var rewriter in rewriters) {
      cancellationToken.ThrowIfCancellationRequested();
      rewriter.PostResolve(program);
    }
  }

  protected virtual Dictionary<TopLevelDeclWithMembers, Dictionary<string, MemberDecl>> ResolveBuiltins(Program program) {
    var systemModuleResolver = new Resolver(this);

    BuiltIns.systemNameInfo = systemModuleResolver.RegisterTopLevelDecls(program.BuiltIns.SystemModule, false);
    systemModuleResolver.moduleInfo = BuiltIns.systemNameInfo;

    systemModuleResolver.RevealAllInScope(program.BuiltIns.SystemModule.TopLevelDecls, BuiltIns.systemNameInfo.VisibilityScope);
    ResolveValueTypeDecls(this);

    // The SystemModule is constructed with all its members already being resolved. Except for
    // the non-null type corresponding to class types.  They are resolved here:
    var systemModuleClassesWithNonNullTypes =
      program.BuiltIns.SystemModule.TopLevelDecls.Where(d => (d as ClassLikeDecl)?.NonNullTypeDecl != null).ToList();
    foreach (var cl in systemModuleClassesWithNonNullTypes) {
      var d = ((ClassLikeDecl)cl).NonNullTypeDecl;
      systemModuleResolver.allTypeParameters.PushMarker();
      systemModuleResolver.ResolveTypeParameters(d.TypeArgs, true, d);
      systemModuleResolver.ResolveType(d.tok, d.Rhs, d, ResolveTypeOptionEnum.AllowPrefix, d.TypeArgs);
      systemModuleResolver.allTypeParameters.PopMarker();
    }

    systemModuleResolver.ResolveTopLevelDecls_Core(
      ModuleDefinition.AllDeclarationsAndNonNullTypeDecls(systemModuleClassesWithNonNullTypes).ToList(),
      new Graph<IndDatatypeDecl>(), new Graph<CoDatatypeDecl>(), program.BuiltIns.SystemModule.Name);

    return systemModuleResolver.moduleClassMembers;
  }

  protected virtual ModuleResolutionResult ResolveModuleDeclaration(CompilationData compilation, ModuleDecl decl) {
    var moduleResolver = new Resolver(this);
    return moduleResolver.ResolveModuleDeclaration(compilation, decl);
  }

  private static void SetHeights(IEnumerable<ModuleDecl> sortedDecls) {
    foreach (var withIndex in sortedDecls.Zip(Enumerable.Range(0, int.MaxValue))) {
      var md = withIndex.First;
      md.Height = withIndex.Second;
      if (md is LiteralModuleDecl literalModuleDecl) {
        var mdef = literalModuleDecl.ModuleDef;
        mdef.Height = withIndex.Second;
      }
    }
  }


  /// <summary>
  /// Check that now two modules that are being compiled have the same CompileName.
  ///
  /// This could happen if they are given the same name using the 'extern' declaration modifier.
  /// </summary>
  /// <param name="prog">The Dafny program being compiled.</param>
  void CheckDupModuleNames(Program prog) {
    // Check that none of the modules have the same CompileName.
    Dictionary<string, ModuleDefinition> compileNameMap = new Dictionary<string, ModuleDefinition>();
    foreach (ModuleDefinition m in prog.CompileModules) {
      var compileIt = true;
      Attributes.ContainsBool(m.Attributes, "compile", ref compileIt);
      if (m.IsAbstract || !compileIt) {
        // the purpose of an abstract module is to skip compilation
        continue;
      }

      string compileName = m.GetCompileName(Options);
      if (compileNameMap.TryGetValue(compileName, out var priorModDef)) {
        Reporter.Error(MessageSource.Resolver, m.tok,
          "modules '{0}' and '{1}' both have CompileName '{2}'",
          priorModDef.tok.val, m.tok.val, compileName);
      } else {
        compileNameMap.Add(compileName, m);
      }
    }
  }

  public static string ModuleNotFoundErrorMessage(int i, List<Name> path, string tail = "") {
    Contract.Requires(path != null);
    Contract.Requires(0 <= i && i < path.Count);
    return "module " + path[i].Value + " does not exist" +
           (1 < path.Count
             ? " (position " + i.ToString() + " in path " + Util.Comma(".", path, x => x.Value) + ")" + tail
             : "");
  }

  private bool ResolveQualifiedModuleIdRootRefines(ModuleDefinition context, ModuleBindings bindings, ModuleQualifiedId qid,
    out ModuleDecl result) {
    Contract.Assert(qid != null);
    IToken root = qid.Path[0].StartToken;
    result = null;
    bool res = bindings.TryLookupFilter(root, out result, m => m.EnclosingModuleDefinition != context);
    return res;
  }

  // Find a matching module for the root of the QualifiedId, ignoring
  // (a) the module (context) itself and (b) any local imports
  // The latter is so that if one writes 'import A`E  import F = A`F' the second A does not
  // resolve to the alias produced by the first import
  private bool ResolveQualifiedModuleIdRootImport(AliasModuleDecl context, ModuleBindings bindings, ModuleQualifiedId qid,
    out ModuleDecl result) {
    Contract.Assert(qid != null);
    IToken root = qid.Path[0].StartToken;
    result = null;
    bool res = bindings.TryLookupFilter(root, out result,
      m => context != m && ((context.EnclosingModuleDefinition == m.EnclosingModuleDefinition && context.Exports.Count == 0) || m is LiteralModuleDecl));
    return res;
  }

  private bool ResolveQualifiedModuleIdRootAbstract(AbstractModuleDecl context, ModuleBindings bindings, ModuleQualifiedId qid,
    out ModuleDecl result) {
    Contract.Assert(qid != null);
    IToken root = qid.Path[0].StartToken;
    result = null;
    bool res = bindings.TryLookupFilter(root, out result,
      m => context != m && ((context.EnclosingModuleDefinition == m.EnclosingModuleDefinition && context.Exports.Count == 0) || m is LiteralModuleDecl));
    return res;
  }

  private void ProcessDependenciesDefinition(ModuleDecl decl, ModuleDefinition m, ModuleBindings bindings,
    Graph<ModuleDecl> dependencies,
    IDictionary<ModuleDecl, Action<ModuleDecl>> declarationPointers) {
    Contract.Assert(decl is LiteralModuleDecl);
    if (m.RefinementQId != null) {
      bool res = ResolveQualifiedModuleIdRootRefines(((LiteralModuleDecl)decl).ModuleDef, bindings, m.RefinementQId, out var other);
      m.RefinementQId.Root = other;
      if (!res) {
        Reporter.Error(MessageSource.Resolver, m.RefinementQId.RootToken(),
          $"module {m.RefinementQId.ToString()} named as refinement base does not exist");
      } else {
        declarationPointers.AddOrUpdate(other, v => m.RefinementQId.Root = v, Util.Concat);
        if (other is LiteralModuleDecl && ((LiteralModuleDecl)other).ModuleDef == m) {
          Reporter.Error(MessageSource.Resolver, m.RefinementQId.RootToken(), "module cannot refine itself: {0}",
            m.RefinementQId.ToString());
        } else {
          Contract.Assert(other != null); // follows from postcondition of TryGetValue
          dependencies.AddEdge(decl, other);
        }
      }
    }

    foreach (var pointer in m.TopLevelDeclPointers) {
      if (pointer.Get() is ModuleDecl moduleDecl) {
        declarationPointers.Add(moduleDecl, v => {
          pointer.Set(v);
          v.EnclosingModuleDefinition = m; // TODO still need test that fails if this line is not here.
        });
      }
    }

    foreach (var toplevel in m.TopLevelDecls) {
      if (toplevel is ModuleDecl) {
        var d = (ModuleDecl)toplevel;
        dependencies.AddEdge(decl, d);
        var subBindings = bindings.SubBindings(d.Name);
        ProcessDependencies(d, subBindings ?? bindings, dependencies, declarationPointers);
        if (!m.IsAbstract && d is AbstractModuleDecl && ((AbstractModuleDecl)d).QId.Root != null) {
          Reporter.Error(MessageSource.Resolver, d.tok,
            "The abstract import named {0} (using :) may only be used in an abstract module declaration",
            d.Name);
        }
      }
    }
  }

  private void ProcessDependencies(ModuleDecl moduleDecl, ModuleBindings bindings,
    Graph<ModuleDecl> dependencies,
    IDictionary<ModuleDecl, Action<ModuleDecl>> declarationPointers) {
    dependencies.AddVertex(moduleDecl);
    if (moduleDecl is LiteralModuleDecl) {
      ProcessDependenciesDefinition(moduleDecl, ((LiteralModuleDecl)moduleDecl).ModuleDef, bindings, dependencies, declarationPointers);
    } else if (moduleDecl is AliasModuleDecl) {
      var alias = moduleDecl as AliasModuleDecl;
      // TryLookupFilter works outward, looking for a match to the filter for
      // each enclosing module.
      if (!ResolveQualifiedModuleIdRootImport(alias, bindings, alias.TargetQId, out var root)) {
        //        if (!bindings.TryLookupFilter(alias.TargetQId.rootToken(), out root, m => alias != m)
        Reporter.Error(MessageSource.Resolver, alias.tok, ModuleNotFoundErrorMessage(0, alias.TargetQId.Path));
      } else {
        alias.TargetQId.Root = root;
        declarationPointers.AddOrUpdate(root, v => alias.TargetQId.Root = v, Util.Concat);
        dependencies.AddEdge(moduleDecl, root);
      }
    } else if (moduleDecl is AbstractModuleDecl) {
      var abs = moduleDecl as AbstractModuleDecl;
      ModuleDecl root;
      if (!ResolveQualifiedModuleIdRootAbstract(abs, bindings, abs.QId, out root)) {
        //if (!bindings.TryLookupFilter(abs.QId.rootToken(), out root,
        //  m => abs != m && (((abs.EnclosingModuleDefinition == m.EnclosingModuleDefinition) && (abs.Exports.Count == 0)) || m is LiteralModuleDecl)))
        Reporter.Error(MessageSource.Resolver, abs.tok, ModuleNotFoundErrorMessage(0, abs.QId.Path));
      } else {
        abs.QId.Root = root;
        declarationPointers.AddOrUpdate(root, v => abs.QId.Root = v, Util.Concat);
        dependencies.AddEdge(moduleDecl, root);
      }
    }
  }
}

enum ValuetypeVariety {
  Bool = 0,
  Int,
  Real,
  BigOrdinal,
  Bitvector,
  Map,
  IMap,
  None
} // note, these are ordered, so they can be used as indices into valuetypeDecls
