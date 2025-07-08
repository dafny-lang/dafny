using System.Linq;
using System.Threading.Tasks;
using System.Threading;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Xunit;
using Xunit.Abstractions;
using XunitAssertMessages;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Various;

public class PluginsTestWithVerification : PluginsTestBase {

  protected override string LibraryName =>
    "PluginsTestVerification";

  protected override string[] CommandLineArgument =>
    [$@"{LibraryPath},""because\\ \""whatever"""];

  [Fact]
  public async Task EnsureItIsPossibleToLoadAPluginAndContinueVerification() {
    // This code will run with the plugin from PluginsAdvancedTest, but that plugin won't throw an exception on the code below.
    var documentItem = CreateTestDocument("function test(): nat { -1 }");
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
    var diagnostics = await GetLastDiagnostics(documentItem);
    AssertM.Equal(2, diagnostics.Length, LibraryPath + " did not raise an error.");
    Assert.Equal("Plugin Error that does not prevent verification", diagnostics[0].Message);
    Assert.Equal("value does not satisfy the subset constraints of 'nat'", diagnostics[1].Message);
    Assert.Equal(new Range((0, 23), (0, 24)), diagnostics[1].Range);
  }

  public PluginsTestWithVerification(ITestOutputHelper output) : base(output) {
  }
}
