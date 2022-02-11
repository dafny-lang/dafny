using Microsoft.Dafny;
using Microsoft.Dafny.Plugins;

public class TestConfiguration : PluginConfiguration {
  public string Argument = "";
  public override void ParseArguments(string[] args) {
    Argument = args[0];
  }
  public override Rewriter[] GetRewriters(ErrorReporter errorReporter) {
    return new Rewriter[] { new ErrorRewriter(errorReporter, this) };
  }
}

public class ErrorRewriter : Rewriter {
  private readonly TestConfiguration configuration;

  public ErrorRewriter(ErrorReporter reporter, TestConfiguration configuration) : base(reporter) {
    this.configuration = configuration;
  }

  public override void PostResolve(ModuleDefinition moduleDefinition) {
    Reporter.Error(MessageSource.Compiler, moduleDefinition.tok, "Impossible to continue " + configuration.Argument);
  }
}