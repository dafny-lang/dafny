using System;
using System.IO;
using System.Text;
using DafnyCore.Test;
using Microsoft.Dafny.LanguageServer.Workspace;
using Xunit.Abstractions;
using Xunit;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest;

public class StandaloneServerTest {
  private readonly TextWriter output;

  public StandaloneServerTest(ITestOutputHelper output) {
    this.output = new WriterFromOutputHelper(output);
  }

  [Fact]
  public void OptionParsing() {
    var arguments = new[] { "--documents:verify=onsave", "--verifier:timelimit=3", "--ghost:markStatements=true" };
    var options = ServerProgram.GetOptionsFromArgs(output, TextReader.Null, arguments);
    Assert.Equal(VerifyOnMode.Save, options.Get(ServerCommand.Verification));
  }
}
