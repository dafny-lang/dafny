using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.VisualStudio.TestTools.UnitTesting;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest;

[TestClass]
public class StandaloneServerTest {

  [TestMethod]
  public void OptionParsing() {
    var arguments = new[] { "--documents:verify=onsave", "--verifier:timelimit=3", "--ghost:markStatements=true" };
    var options = OldCliProgram.GetOptionsFromArgs(arguments);
    Assert.AreEqual(VerifyOnMode.Save, options.Get(ServerCommand.Verification));
  }
}
