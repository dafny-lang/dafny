using System.Linq;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Xunit.Abstractions;
using Xunit;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Various;

public class PluginsDafnyCodeActionTest : PluginsTestBase {

  protected override string LibraryName =>
    "PluginsDafnyCodeActionTest";

  protected override string[] CommandLineArgument =>
    new[] { $"{LibraryPath}" };

  [Fact]
  public async Task EnsureDafnyCodeActionProviderWorks() {
    var documentItem = CreateTestDocument(@"
method firstMethod() {
}");
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
    var codeActionResult = await client.RequestCodeAction(new CodeActionParams {
      TextDocument = documentItem.Uri.GetFileSystemPath(),
      Range = ((0, 0), (0, 0))
    },
      CancellationToken);
    Assert.Single(codeActionResult);
    var codeAction = codeActionResult.ToList()[0].CodeAction;
    Assert.NotNull(codeAction);
    Assert.Equal("Insert file header", codeAction.Title);
    // The rest is tested elsewhere
  }

  public PluginsDafnyCodeActionTest(ITestOutputHelper output) : base(output)
  {
  }
}
