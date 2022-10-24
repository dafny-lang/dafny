using System;
using Microsoft.Dafny;
using Microsoft.Dafny.Plugins;

namespace PluginsTestVerification {

  public class TestConfiguration : PluginConfiguration {
    public override Rewriter[] GetRewriters(ErrorReporter errorReporter) {
      return new Rewriter[] { new ErrorRewriter(errorReporter) };
    }
  }

  public class ErrorRewriter : Rewriter {
    public ErrorRewriter(ErrorReporter reporter) : base(reporter) {
    }

    public override void PostResolve(Program program) {
      Reporter.Error(MessageSource.Compiler, program.GetFirstTopLevelToken(),
        "Plugin Error that does not prevent verification");
    }
  }

}