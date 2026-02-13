using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class TriggerGeneratingRewriter : IRewriter {
  private readonly SystemModuleManager systemModuleManager;
  internal TriggerGeneratingRewriter(ErrorReporter reporter, SystemModuleManager systemModuleManager) : base(reporter) {
    Contract.Requires(reporter != null);
    this.systemModuleManager = systemModuleManager;
  }

  internal override void PostCyclicityResolve(ModuleDefinition definition) {
    var finder = new Triggers.QuantifierCollector(Reporter);

    foreach (var decl in ModuleDefinition.AllCallablesIncludingPrefixDeclarations(definition.TopLevelDecls)) {
      finder.Visit(decl, null);
    }

    var triggersCollector = new Triggers.TriggersCollector(finder.exprsInOldContext, Reporter.Options, definition);
    foreach (var quantifierCollection in finder.quantifierCollections) {
      quantifierCollection.ComputeTriggers(triggersCollector);
      quantifierCollection.CommitTriggers(systemModuleManager);
    }

    finder.ApplyPostActions();
  }
}