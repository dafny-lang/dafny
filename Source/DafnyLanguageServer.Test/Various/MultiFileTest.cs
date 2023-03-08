using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using OmniSharp.Extensions.LanguageServer.Protocol.Client;
using System.IO;
using System.Linq;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.Workspace;
using Xunit.Abstractions;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Various {

  [TestClass]
  public class MultiFileTest : DafnyLanguageServerTestBase {
    private static readonly string TestFilePath = Path.Combine(Directory.GetCurrentDirectory(), "Various", "TestFiles", "testFile.dfy");

    private ILanguageClient client;

    [TestInitialize]
    public async Task SetUp() {
      client = await InitializeClient();
    }

    // https://github.com/dafny-lang/language-server-csharp/issues/40
    [TestMethod]
    public async Task ImplicitlyIncludingTheSameModuleTwiceDoesNotResultInDuplicateError() {
      var source = @"
include ""multi1.dfy""
include ""multi2.dfy""

method Test() {
  assert true;
}";
      var documentItem = CreateTestDocument(source, TestFilePath);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var document = await Documents.GetResolvedDocumentAsync(documentItem.Uri);
      Assert.IsNotNull(document);
      Assert.IsTrue(!document.Diagnostics.Any());
    }

    // https://github.com/dafny-lang/language-server-csharp/issues/40
    [TestMethod]
    public async Task ImplicitlyIncludingTheSameModuleTwiceDoesNotOverrideActualError() {
      var source = @"
include ""multi1.dfy""
include ""multi2.dfy""

method Test() {
  assert false;
}";
      var documentItem = CreateTestDocument(source, TestFilePath);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var document = await Documents.GetLastDocumentAsync(documentItem.Uri);
      Assert.IsNotNull(document);
      Assert.AreEqual(1, document.Diagnostics.Count());
    }

    public MultiFileTest(ITestOutputHelper output) : base(output)
    {
    }
  }
}
