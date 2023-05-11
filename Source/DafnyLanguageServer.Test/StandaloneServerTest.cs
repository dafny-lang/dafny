using Microsoft.Dafny.LanguageServer.Workspace;
using Xunit;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest;

public class StandaloneServerTest {

  [Fact]
  public void OptionParsing() {
    var arguments = new[] { "--documents:verify=onsave", "--verifier:timelimit=3", "--ghost:markStatements=true" };
    var options = Program.GetOptionsFromArgs(arguments);
    Assert.Equal(VerifyOnMode.Save, options.Get(ServerCommand.Verification));
  }
}
