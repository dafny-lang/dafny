using Microsoft.Dafny;
using Microsoft.Dafny.Plugins;

public class TestConfiguration : PluginConfiguration {
  public string Argument = "";
  public override void ParseArguments(string[] args) {
    Argument = args[0];
  }
  public override Rewriter[] GetRewriters(ErrorReporter errorReporter) {
    return new Rewriter[] { new RewriterPreventingVerificationWithArgument(errorReporter, this) };
  }
}

public class RewriterPreventingVerificationWithArgument : Rewriter {
  private readonly TestConfiguration configuration;

  public RewriterPreventingVerificationWithArgument(ErrorReporter reporter, TestConfiguration configuration) : base(reporter) {
    this.configuration = configuration;
  }

  public override void PostResolve(ModuleDefinition moduleDefinition) {
    Reporter.Error(MessageSource.Resolver, moduleDefinition.Tok, "Impossible to continue " + configuration.Argument);
  }
}