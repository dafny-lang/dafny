using System.Diagnostics.Contracts;

namespace Microsoft.Dafny;

public class TriggerGeneratingRewriter : IRewriter {
  internal TriggerGeneratingRewriter(ErrorReporter reporter) : base(reporter) {
    Contract.Requires(reporter != null);
  }

  internal override void PostCyclicityResolve(ModuleDefinition definition, ErrorReporter reporter) {
    var finder = new Triggers.QuantifierCollector(reporter);

    foreach (var decl in ModuleDefinition.AllCallablesIncludingPrefixDeclarations(definition.TopLevelDecls)) {
      finder.Visit(decl, null);
    }

    var triggersCollector = new Triggers.TriggersCollector(finder.exprsInOldContext, Reporter.Options);
    foreach (var quantifierCollection in finder.quantifierCollections) {
      quantifierCollection.ComputeTriggers(triggersCollector);
      quantifierCollection.CommitTriggers(Reporter.Options);
    }
  }
}