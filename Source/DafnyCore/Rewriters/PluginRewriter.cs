namespace Microsoft.Dafny;

class PluginRewriter(ErrorReporter reporter, Plugins.Rewriter internalRewriter) : IRewriter(reporter) {
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