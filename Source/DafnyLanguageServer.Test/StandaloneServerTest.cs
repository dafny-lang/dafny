using System;
using System.IO;
using System.Text;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using Xunit;
using Xunit.Abstractions;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest;

public class StandaloneServerTest {

  private readonly TextWriter output;

  public StandaloneServerTest(ITestOutputHelper output) {
    this.output = new WriterFromOutputHelper(output);
  }

  [Fact]
  public void OptionParsing() {
    var arguments = new[] { "--documents:verify=onsave", "--verifier:timelimit=3", "--ghost:markStatements=true" };
    var options = Program.GetOptionsFromArgs(output, arguments);
    Assert.AreEqual(VerifyOnMode.Save, options.Get(ServerCommand.Verification));
  }
}

public class WriterFromOutputHelper : TextWriter {
  private readonly ITestOutputHelper output;

  public WriterFromOutputHelper(ITestOutputHelper output) {
    this.output = output;
  }

  public override void Write(char value) {
    throw new NotSupportedException();
  }

  public override Encoding Encoding => Encoding.Default;

  public override void WriteLine(string value) {
    output.WriteLine(value);
  }

  public override void WriteLine(string format, params object[] arg) {
    output.WriteLine(format, arg);
  }
}
