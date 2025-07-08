namespace Microsoft.Dafny;

class PluginRewriter : IRewriter {
  private Plugins.Rewriter internalRewriter;

  public PluginRewriter(ErrorReporter reporter, Plugins.Rewriter internalRewriter) : base(reporter) {
    this.internalRewriter = internalRewriter;
  }

  internal override void PostResolve(ModuleDefinition moduleDefinition) {
    internalRewriter.PostResolve(moduleDefinition);
  }

  internal override void PostResolve(Program program) {
    internalRewriter.PostResolve(program);
  }

  internal override void PreResolve(ModuleDefinition module) {
    internalRewriter.PreResolve(module);
  }

  internal override void PreVerify(ModuleDefinition module) {
    internalRewriter.PreVerify(module);
  }
}