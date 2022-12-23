namespace Microsoft.Dafny;

// TODO should this move to a verifier folder?
public class TriggerGeneratingRewriter : IRewriter {
  internal TriggerGeneratingRewriter(ErrorReporter reporter) : base(reporter) {
    Contract.Requires(reporter != null);
  }

  internal override void PostCyclicityResolve(ModuleDefinition m) {
    var finder = new Triggers.QuantifierCollector(Reporter);

    foreach (var decl in ModuleDefinition.AllCallablesIncludingPrefixDeclarations(m.TopLevelDecls)) {
      finder.Visit(decl, null);
    }

    var triggersCollector = new Triggers.TriggersCollector(finder.exprsInOldContext);
    foreach (var quantifierCollection in finder.quantifierCollections) {
      quantifierCollection.ComputeTriggers(triggersCollector);
      quantifierCollection.CommitTriggers();
    }
  }
}