using System.Linq;
using System.Threading.Tasks;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using System.Threading;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Various;

[TestClass]
public class PluginsTest : PluginsTestBase {
  [TestInitialize]
  public async Task SetUp() {
    await SetUpPlugin();
  }
  protected override string LibraryCode =>
    @"
using Microsoft.Dafny;
using Microsoft.Dafny.Plugins;

namespace PluginsTest {

public class TestConfiguration: PluginConfiguration {
  public string Argument = """";
  public override void ParseArguments(string[] args) {
    Argument = args.Length > 0 ? args[0] : ""[no argument]"";
  }
  public override Rewriter[] GetRewriters(ErrorReporter errorReporter) {
    return new Rewriter[]{new ErrorRewriter(errorReporter, this)};
  }
}

public class ErrorRewriter: Rewriter {
  private readonly TestConfiguration configuration;

  public ErrorRewriter(ErrorReporter reporter, TestConfiguration configuration): base(reporter) {
    this.configuration = configuration;
  }

  public override void PostResolve(ModuleDefinition moduleDefinition) {
    Reporter.Error(MessageSource.Compiler, moduleDefinition.GetFirstTopLevelToken(), ""Impossible to continue ""+configuration.Argument);
  }
}

}";

  protected override string LibraryName =>
    "PluginsTest";

  protected override string[] CommandLineArgument =>
    new[] { $@"--dafny:plugins:0=""{LibraryPath},\""because\\ whatever\""""" };

  [TestMethod]
  public async Task EnsureItIsPossibleToLoadAPluginWithArguments() {
    // This code will run with the plugin from PluginsAdvancedTest, but that plugin won't throw an exception on the code below.
    var documentItem = CreateTestDocument("function test(): int { 1 }");
    await Client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
    var resolutionReport = await DiagnosticReceiver.AwaitNextNotificationAsync(CancellationToken.None);
    Assert.AreEqual(documentItem.Uri, resolutionReport.Uri);
    var diagnostics = resolutionReport.Diagnostics.ToArray();
    Assert.AreEqual(DafnyOptions.O.Plugins.Count, 1, "Too many plugins loaded");
    Assert.AreEqual(1, diagnostics.Length, LibraryPath + " did not raise an error.");
    Assert.AreEqual("Impossible to continue because\\ whatever", diagnostics[0].Message);
    Assert.AreEqual(new Range((0, 9), (0, 13)), diagnostics[0].Range);
  }

  [TestCleanup]
  public void DoCleanup() {
    CleanupPlugin();
  }
}
