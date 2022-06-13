using Microsoft.Dafny;
using Microsoft.Dafny.Plugins;

public class RewriterAllowingVerification : Rewriter {
  public RewriterAllowingVerification(ErrorReporter reporter) : base(reporter) { }

  public override void PostResolve(Program program) {
    Reporter.Error(MessageSource.Compiler, program.GetFirstTopLevelToken(), "Verification may proceed");
  }
}