using Microsoft.Dafny;
using Microsoft.Dafny.Plugins;

public class ErrorRewriter : Rewriter {
  public ErrorRewriter(ErrorReporter reporter) : base(reporter) { }

  public override void PostResolve(ModuleDefinition moduleDefinition) {
    Reporter.Error(MessageSource.Compiler, moduleDefinition.tok, "Impossible to continue");
  }
}