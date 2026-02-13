using Microsoft.Dafny;
using Microsoft.Dafny.Plugins;

public class RewriterPreventingVerification : Rewriter {
  public RewriterPreventingVerification(ErrorReporter reporter) : base(reporter) { }

  public override void PostResolve(ModuleDefinition moduleDefinition) {
    Reporter.Error(MessageSource.Resolver, moduleDefinition.Origin, "Impossible to continue");
  }
}