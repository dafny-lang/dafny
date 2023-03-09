using System.Linq;
using System.Threading.Tasks;
using System.Threading;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Xunit;
using XunitAssertMessages;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Various;

public class PluginsTestWithVerification : PluginsTestBase {

  protected override string LibraryName =>
    "PluginsTestVerification";

  protected override string[] CommandLineArgument =>
    new[] { $@"{LibraryPath},""because\\ \""whatever""" };

  [Fact]
  public async Task EnsureItIsPossibleToLoadAPluginAndContinueVerification() {
    // This code will run with the plugin from PluginsAdvancedTest, but that plugin won't throw an exception on the code below.
    var documentItem = CreateTestDocument("function test(): nat { -1 }");
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
    var resolutionReport = await diagnosticsReceiver.AwaitNextNotificationAsync(CancellationToken.None);
    Assert.Equal(documentItem.Uri, resolutionReport.Uri);
    var verificationReport = await diagnosticsReceiver.AwaitNextNotificationAsync(CancellationToken.None);
    Assert.Equal(documentItem.Uri, resolutionReport.Uri);
    var diagnostics = verificationReport.Diagnostics.ToArray();
    AssertM.Equal(2, diagnostics.Length, LibraryPath + " did not raise an error.");
    Assert.Equal("Plugin Error that does not prevent verification", diagnostics[0].Message, null);
    Assert.Equal(new Range((0, 0), (0, 8)), diagnostics[0].Range);
    Assert.Equal("value does not satisfy the subset constraints of 'nat'", diagnostics[1].Message, null);
    Assert.Equal(new Range((0, 23), (0, 24)), diagnostics[1].Range);
  }
}
