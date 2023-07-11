using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using System.Threading;

namespace Microsoft.Dafny; 

public class ProgramResolver {
  public Program Program { get; }

  private readonly Dictionary<TopLevelDeclWithMembers, Dictionary<string, MemberDecl>> classMembers = new();

  protected readonly Graph<ModuleDecl> dependencies = new();
  public DafnyOptions Options => Program.Options;
  public SystemModuleManager SystemModuleManager => Program.SystemModuleManager;
  public ErrorReporter Reporter => Program.Reporter;

  public ProgramResolver(Program program) {
    Program = program;
  }

  public Dictionary<string, MemberDecl> GetClassMembers(TopLevelDeclWithMembers key) {
    if (classMembers.TryGetValue(key, out var result)) {
      return result;
    }
    return null;
  }

  public void Resolve(CancellationToken cancellationToken) {
    Type.ResetScopes();

    Type.EnableScopes();
    // For the formatter, we ensure we take snapshots of the PrefixNamedModules and topleveldecls
    Program.DefaultModuleDef.PreResolveSnapshotForFormatter();

    // Changing modules at this stage without changing their CloneId doesn't break resolution caching,
    // because ResolvedPrefixNamedModules end up in the dependencies of a module so they change its hash anyways
    Program.DefaultModuleDef.ProcessPrefixNamedModules();

    var startingErrorCount = Reporter.ErrorCount;
    ComputeModuleDependencyGraph(Program, out var moduleDeclarationPointers);

    if (Reporter.ErrorCount != startingErrorCount) {
      return;
    }

    var sortedDecls = dependencies.TopologicallySortedComponents();
    Program.ModuleSigs = new();

    SetHeights(sortedDecls);

    var systemClassMembers = ResolveSystemModule(Program);
    foreach (var moduleClassMembers in systemClassMembers) {
      classMembers[moduleClassMembers.Key] = moduleClassMembers.Value;
    }

    var compilation = Program.Compilation;
    foreach (var rewriter in compilation.Rewriters) {
      cancellationToken.ThrowIfCancellationRequested();
      rewriter.PreResolve(Program);
    }

    foreach (var decl in sortedDecls) {
      cancellationToken.ThrowIfCancellationRequested();
      var moduleResolutionResult = ResolveModuleDeclaration(compilation, decl);
      ProcessDeclarationResolutionResult(moduleDeclarationPointers, decl, moduleResolutionResult);
    }

    if (Reporter.ErrorCount != startingErrorCount) {
      return;
    }

    Type.DisableScopes();

    CheckDuplicateModuleNames(Program);

    foreach (var rewriter in compilation.Rewriters) {
      cancellationToken.ThrowIfCancellationRequested();
      rewriter.PostResolve(Program);
    }
  }

  private void ProcessDeclarationResolutionResult(Dictionary<ModuleDecl, Action<ModuleDecl>> moduleDeclarationPointers, ModuleDecl decl,
    ModuleResolutionResult moduleResolutionResult) {
    moduleDeclarationPointers[decl](moduleResolutionResult.ResolvedDeclaration);

    foreach (var sig in moduleResolutionResult.Signatures) {
      Program.ModuleSigs[sig.Key] = sig.Value;
    }

    foreach (var moduleClassMembers in moduleResolutionResult.ClassMembers) {
      classMembers[moduleClassMembers.Key] = moduleClassMembers.Value;
    }

    foreach (var diagnostic in moduleResolutionResult.ErrorReporter.AllMessages) {
      Reporter.Message(diagnostic.Source, diagnostic.Level, diagnostic.ErrorId, diagnostic.Token,
        diagnostic.Message);
    }
  }

  /// <summary>
  /// We determine where pointers to module declarations occur, and store those so caching can later set those.
  /// </summary>
  private void ComputeModuleDependencyGraph(Program program, out Dictionary<ModuleDecl, Action<ModuleDecl>> moduleDeclarationPointers) {
    var startingErrorCount = Reporter.ErrorCount;
    var rootBindings = new ModuleBindings(null);
    // TODO can we delete rootBindings and pass null instead?
    var defaultModuleBindings = program.DefaultModuleDef.BindModuleNames(this, rootBindings);
    rootBindings.BindName(program.DefaultModule.Name, program.DefaultModule, defaultModuleBindings);

    if (Reporter.ErrorCount != startingErrorCount) {
      // if there were errors, then the implicit ModuleBindings data structure invariant
      // is violated, so Processing dependencies will not succeed.
      moduleDeclarationPointers = null;
      return;
    }

    moduleDeclarationPointers = new();
    moduleDeclarationPointers[program.DefaultModule] = v => program.DefaultModule = (LiteralModuleDecl)v;
    ProcessDependencies(program.DefaultModule, defaultModuleBindings, moduleDeclarationPointers);

    // check for cycles in the import graph
    foreach (var cycle in dependencies.AllCycles()) {
      ModuleResolver.ReportCycleError(Reporter, cycle, m => m.tok,
        m => (m is AliasModuleDecl ? "import " : "module ") + m.Name,
        "module definition contains a cycle (note: parent modules implicitly depend on submodules)");
    }
  }

  protected virtual Dictionary<TopLevelDeclWithMembers, Dictionary<string, MemberDecl>> ResolveSystemModule(Program program) {
    var systemModuleResolver = new ModuleResolver(this);

    SystemModuleManager.systemNameInfo = SystemModuleManager.SystemModule.RegisterTopLevelDecls(systemModuleResolver, false);
    systemModuleResolver.moduleInfo = SystemModuleManager.systemNameInfo;

    systemModuleResolver.RevealAllInScope(SystemModuleManager.SystemModule.TopLevelDecls, SystemModuleManager.systemNameInfo.VisibilityScope);
    SystemModuleManager.ResolveValueTypeDecls(this);

    // The SystemModule is constructed with all its members already being resolved. Except for
    // the non-null type corresponding to class types.  They are resolved here:
    var systemModuleClassesWithNonNullTypes =
      SystemModuleManager.SystemModule.TopLevelDecls.Where(d => (d as ClassLikeDecl)?.NonNullTypeDecl != null).ToList();
    foreach (var cl in systemModuleClassesWithNonNullTypes) {
      var d = ((ClassLikeDecl)cl).NonNullTypeDecl;
      systemModuleResolver.allTypeParameters.PushMarker();
      systemModuleResolver.ResolveTypeParameters(d.TypeArgs, true, d);
      systemModuleResolver.ResolveType(d.tok, d.Rhs, d, ResolveTypeOptionEnum.AllowPrefix, d.TypeArgs);
      systemModuleResolver.allTypeParameters.PopMarker();
    }

    systemModuleResolver.ResolveTopLevelDecls_Core(
      ModuleDefinition.AllDeclarationsAndNonNullTypeDecls(systemModuleClassesWithNonNullTypes).ToList(),
      new Graph<IndDatatypeDecl>(), new Graph<CoDatatypeDecl>(), SystemModuleManager.SystemModule.Name);

    return systemModuleResolver.moduleClassMembers;
  }

  protected virtual ModuleResolutionResult ResolveModuleDeclaration(CompilationData compilation, ModuleDecl decl) {
    var moduleResolver = new ModuleResolver(this);
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
  /// <param name="program">The Dafny program being compiled.</param>
  private void CheckDuplicateModuleNames(Program program) {
    // Check that none of the modules have the same CompileName.
    Dictionary<string, ModuleDefinition> compileNameMap = new Dictionary<string, ModuleDefinition>();
    foreach (ModuleDefinition m in program.CompileModules) {
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
    var addendum = 1 < path.Count ? $" (position {i} in path {Util.Comma(".", path, x => x.Value)}){tail}" : "";
    return
      $"module {path[i].Value} does not exist" + addendum;
  }

  private void ProcessDependenciesDefinition(LiteralModuleDecl literalDecl, ModuleBindings bindings,
    IDictionary<ModuleDecl, Action<ModuleDecl>> declarationPointers) {
    var module = literalDecl.ModuleDef;
    if (module.RefinementQId != null) {
      bool res = bindings.ResolveQualifiedModuleIdRootRefines(literalDecl.ModuleDef, module.RefinementQId, out var other);
      module.RefinementQId.Root = other;
      if (!res) {
        Reporter.Error(MessageSource.Resolver, module.RefinementQId.RootToken(),
          $"module {module.RefinementQId} named as refinement base does not exist");
      } else {
        declarationPointers.AddOrUpdate(other, v => module.RefinementQId.Root = v, Util.Concat);
        if (other is LiteralModuleDecl otherLiteral && otherLiteral.ModuleDef == module) {
          Reporter.Error(MessageSource.Resolver, module.RefinementQId.RootToken(), "module cannot refine itself: {0}",
            module.RefinementQId.ToString());
        } else {
          Contract.Assert(other != null); // follows from postcondition of TryGetValue
          dependencies.AddEdge(literalDecl, other);
        }
      }
    }

    foreach (var pointer in module.TopLevelDeclPointers) {
      if (pointer.Get() is ModuleDecl moduleDecl) {
        declarationPointers.Add(moduleDecl, v => {
          pointer.Set(v);
          v.EnclosingModuleDefinition = module;
          if (v is LiteralModuleDecl literalModuleDecl) {
            literalModuleDecl.ModuleDef.EnclosingModule = module;
          }
        });
      }
    }

    foreach (var toplevel in module.TopLevelDecls) {
      if (toplevel is not ModuleDecl moduleDecl) {
        continue;
      }

      dependencies.AddEdge(literalDecl, moduleDecl);
      var subBindings = bindings.SubBindings(moduleDecl.Name);
      ProcessDependencies(moduleDecl, subBindings ?? bindings, declarationPointers);
      if (!module.IsAbstract && moduleDecl is AbstractModuleDecl && ((AbstractModuleDecl)moduleDecl).QId.Root != null) {
        Reporter.Error(MessageSource.Resolver, moduleDecl.tok,
          "The abstract import named {0} (using :) may only be used in an abstract module declaration",
          moduleDecl.Name);
      }
    }
  }

  private void ProcessDependencies(ModuleDecl moduleDecl, ModuleBindings bindings,
    IDictionary<ModuleDecl, Action<ModuleDecl>> declarationPointers) {
    dependencies.AddVertex(moduleDecl);
    if (moduleDecl is LiteralModuleDecl literalDecl) {
      ProcessDependenciesDefinition(literalDecl, bindings, declarationPointers);
    } else if (moduleDecl is AliasModuleDecl aliasDecl) {
      // TryLookupFilter works outward, looking for a match to the filter for
      // each enclosing module.
      if (!bindings.ResolveQualifiedModuleIdRootImport(aliasDecl, aliasDecl.TargetQId, out var root)) {
        //        if (!bindings.TryLookupFilter(alias.TargetQId.rootToken(), out root, m => alias != m)
        Reporter.Error(MessageSource.Resolver, aliasDecl.tok, ModuleNotFoundErrorMessage(0, aliasDecl.TargetQId.Path));
      } else {
        aliasDecl.TargetQId.Root = root;
        declarationPointers.AddOrUpdate(root, v => aliasDecl.TargetQId.Root = v, Util.Concat);
        dependencies.AddEdge(aliasDecl, root);
      }
    } else if (moduleDecl is AbstractModuleDecl abstractDecl) {
      if (!bindings.ResolveQualifiedModuleIdRootAbstract(abstractDecl, abstractDecl.QId, out var root)) {
        //if (!bindings.TryLookupFilter(abs.QId.rootToken(), out root,
        //  m => abs != m && (((abs.EnclosingModuleDefinition == m.EnclosingModuleDefinition) && (abs.Exports.Count == 0)) || m is LiteralModuleDecl)))
        Reporter.Error(MessageSource.Resolver, abstractDecl.tok, ModuleNotFoundErrorMessage(0, abstractDecl.QId.Path));
      } else {
        abstractDecl.QId.Root = root;
        declarationPointers.AddOrUpdate(root, v => abstractDecl.QId.Root = v, Util.Concat);
        dependencies.AddEdge(abstractDecl, root);
      }
    }
  }
}
