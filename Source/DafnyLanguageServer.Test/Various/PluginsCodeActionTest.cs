using System.Linq;
using System.Threading.Tasks;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using System.Threading;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Extensions.DependencyModel;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Various;

[TestClass]
public class PluginsDafnyCodeActionTest : PluginsTestBase {

  protected override string LibraryName =>
    "PluginsDafnyCodeActionTest";

  protected override string[] CommandLineArgument =>
    new[] { $"{LibraryPath}" };

  [TestMethod]
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
    Assert.AreEqual(1, codeActionResult.Count());
    var codeAction = codeActionResult.ToList()[0].CodeAction;
    Assert.IsNotNull(codeAction);
    Assert.AreEqual("Insert file header", codeAction.Title);
    // The rest is tested elsewhere
  }
}
