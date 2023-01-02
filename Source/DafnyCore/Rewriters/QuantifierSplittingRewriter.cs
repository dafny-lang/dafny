namespace Microsoft.Dafny;

internal class QuantifierSplittingRewriter : IRewriter {
  internal QuantifierSplittingRewriter(ErrorReporter reporter) : base(reporter) {
    Contract.Requires(reporter != null);
  }

  internal override void PostResolveIntermediate(ModuleDefinition m) {
    var splitter = new Triggers.QuantifierSplitter();
    foreach (var decl in ModuleDefinition.AllCallables(m.TopLevelDecls)) {
      splitter.Visit(decl);
    }
    splitter.Commit();
  }
}