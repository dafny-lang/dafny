using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;
using Microsoft.Dafny.Auditor;

namespace Microsoft.Dafny;

public class Program : TokenNode {
  public CompilationData Compilation { get; }

  [ContractInvariantMethod]
  void ObjectInvariant() {
    Contract.Invariant(FullName != null);
    Contract.Invariant(DefaultModule != null);
  }

  public readonly string FullName;

  // Resolution essentially flattens the module hierarchy, for
  // purposes of translation and compilation.
  [FilledInDuringResolution] public Dictionary<ModuleDefinition, ModuleSignature> ModuleSigs;
  [FilledInDuringResolution] public IEnumerable<ModuleDefinition> CompileModules => new[] { SystemModuleManager.SystemModule }.Concat(Modules());
  // Contains the definitions to be used for compilation.

  public Method MainMethod; // Method to be used as main if compiled
  public LiteralModuleDecl DefaultModule;
  public IList<FileModuleDefinition> Files { get; } = new List<FileModuleDefinition>();
  public DefaultModuleDefinition DefaultModuleDef => (DefaultModuleDefinition)DefaultModule.ModuleDef;
  public SystemModuleManager SystemModuleManager;
  public DafnyOptions Options => Reporter.Options;
  public ErrorReporter Reporter { get; set; }

  public Program(string name, [Captured] LiteralModuleDecl module, [Captured] SystemModuleManager systemModuleManager, ErrorReporter reporter,
    CompilationData compilation) {
    Contract.Requires(name != null);
    Contract.Requires(module != null);
    Contract.Requires(reporter != null);
    FullName = name;
    DefaultModule = module;
    SystemModuleManager = systemModuleManager;
    Reporter = reporter;
    Compilation = compilation;
  }

  //Set appropriate visibilty before presenting module
  public IEnumerable<ModuleDefinition> Modules() {

    foreach (var msig in ModuleSigs) {
      Type.PushScope(msig.Value.VisibilityScope);
      yield return msig.Key;
      Type.PopScope(msig.Value.VisibilityScope);
    }

  }

  public IEnumerable<ModuleDefinition> RawModules() {
    return ModuleSigs.Keys;
  }

  public string Name {
    get {
      try {
        return System.IO.Path.GetFileName(FullName);
      } catch (ArgumentException) {
        return FullName;
      }
    }
  }

  /// Get the first token that is in the same file as the DefaultModule.RootToken.FileName
  /// (skips included tokens)
  public IToken GetFirstTopLevelToken() {
    var rootToken = DefaultModuleDef.RangeToken.StartToken;
    if (rootToken.Next == null) {
      return null;
    }

    var firstToken = rootToken;
    // We skip all included files
    while (firstToken is { Next: { } } && firstToken.Next.Filepath != rootToken.Filepath) {
      firstToken = firstToken.Next;
    }

    if (firstToken == null || firstToken.kind == 0) {
      return null;
    }

    return firstToken;
  }

  public override IEnumerable<Node> Children => new[] { DefaultModule };

  public override IEnumerable<Node> PreResolveChildren => Children;

  public override IEnumerable<Assumption> Assumptions(Declaration decl) {
    return Modules().SelectMany(m => m.Assumptions(decl));
  }
}

[AttributeUsage(AttributeTargets.Field | AttributeTargets.Property)]
public class FilledInDuringTranslationAttribute : Attribute { }
[AttributeUsage(AttributeTargets.Field | AttributeTargets.Property)]
public class FilledInDuringResolutionAttribute : Attribute { }