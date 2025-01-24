using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Xunit.Abstractions;
using Xunit;
using System.Threading;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Various;

public class PluginsHandlerTest : PluginsTestBase {

  protected override string LibraryName =>
    "PluginsHandlerTest";

  protected override string[] CommandLineArgument =>
    [$"{LibraryPath}"];

  [Fact]
  public async Task EnsureWithPluginHandlersWorks() {
    var documentItem = CreateTestDocument(@"
method firstMethod() {
}");
    var cancellationToken = new CancellationToken();
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
    var requestResult = await client.SendRequest("dafny/request/dummy").Returning<string>(cancellationToken);
    Assert.Equal("dummy", requestResult);
  }

  public PluginsHandlerTest(ITestOutputHelper output) : base(output) {
  }
}
