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

  public ProofDependencyManager ProofDependencyManager { get; set; } = new();

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

  public Program(Cloner cloner, Program original) {
    FullName = original.FullName;
    DefaultModule = new LiteralModuleDecl(cloner, original.DefaultModule, original.DefaultModule.EnclosingModuleDefinition);
    Files = original.Files;
    SystemModuleManager = original.SystemModuleManager;
    Reporter = original.Reporter;
    Compilation = original.Compilation;

    if (cloner.CloneResolvedFields) {
      throw new NotImplementedException();
    }
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
  public IToken GetStartOfFirstFileToken() {
    return GetFirstTokenForUri(Compilation.RootSourceUris[0]);
  }

  public IToken GetFirstTokenForUri(Uri uri) {
    return this.FindNodesInUris(uri).MinBy(n => n.RangeToken.StartToken.pos)?.StartToken;
  }

  public override IEnumerable<INode> Children => new[] { DefaultModule };

  public override IEnumerable<INode> PreResolveChildren => DefaultModuleDef.Includes.Concat<INode>(Files);

  public override IEnumerable<Assumption> Assumptions(Declaration decl) {
    return Modules().SelectMany(m => m.Assumptions(decl));
  }
}

[AttributeUsage(AttributeTargets.Field | AttributeTargets.Property)]
public class FilledInDuringTranslationAttribute : Attribute { }
[AttributeUsage(AttributeTargets.Field | AttributeTargets.Property)]
public class FilledInDuringResolutionAttribute : Attribute { }