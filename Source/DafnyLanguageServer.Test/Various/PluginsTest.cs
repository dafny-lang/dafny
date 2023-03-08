using System.Linq;
using System.Threading.Tasks;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using System.Threading;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Xunit.Abstractions;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Various;

[TestClass]
public class PluginsTest : PluginsTestBase {

  protected override string LibraryName =>
    "PluginsTest";

  protected override string[] CommandLineArgument =>
    new[] { $@"{LibraryPath},""because\\ \""whatever""" };

  [TestMethod]
  public async Task EnsureItIsPossibleToLoadAPluginWithArguments() {
    // This code will run with the plugin from PluginsAdvancedTest, but that plugin won't throw an exception on the code below.
    var documentItem = CreateTestDocument("function test(): int { 1 }");
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
    var resolutionReport = await diagnosticsReceiver.AwaitNextNotificationAsync(CancellationToken.None);
    Assert.AreEqual(documentItem.Uri, resolutionReport.Uri);
    var diagnostics = resolutionReport.Diagnostics.ToArray();
    Assert.AreEqual(1, diagnostics.Length, LibraryPath + " did not raise an error.");
    Assert.AreEqual("Impossible to continue because\\ \"whatever", diagnostics[0].Message);
    Assert.AreEqual(new Range((0, 0), (0, 8)), diagnostics[0].Range);
  }

  public PluginsTest(ITestOutputHelper output) : base(output)
  {
  }
}
