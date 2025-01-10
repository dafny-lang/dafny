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

    public override void PreVerify(ModuleDefinition module) {
      Reporter.Error(MessageSource.Compiler, Token.NoToken,
        "Plugin Error that does not prevent verification");
    }
  }

}