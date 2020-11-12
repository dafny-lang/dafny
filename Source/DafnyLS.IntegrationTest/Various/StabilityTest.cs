using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using OmniSharp.Extensions.LanguageServer.Protocol.Client;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.IO;
using System.Threading.Tasks;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Stability {
  /// <summary>
  /// These integration tests involve various complex programs that are used
  /// to ensure that the language server is capable to load. It helps to ensure
  /// that for example syntax nodes are correctly visited.
  /// </summary>
  [TestClass]
  public class StabilityTest : DafnyLanguageServerTestBase {
    private ILanguageClient _client;
    private const int MaxTestExecutionTimeMs = 60000;

    private async Task<TextDocumentItem> CreateTextDocumentFromFileAsync(string fileName) {
      var filePath = Path.Combine("Various", "TestFiles", fileName);
      var source = await File.ReadAllTextAsync(filePath, CancellationToken);
      return CreateTestDocument(source);
    }

    [TestInitialize]
    public async Task SetUp() {
      _client = await InitializeClient();
    }

    [TestMethod]
    [Timeout(MaxTestExecutionTimeMs)]
    public async Task GhcMergeSort() {
      var documentItem = await CreateTextDocumentFromFileAsync("GHC-MergeSort.dfy");
      await _client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      Assert.IsTrue(Documents.TryGetDocument(documentItem.Uri, out var _));
    }

    [TestMethod]
    [Timeout(MaxTestExecutionTimeMs)]
    public async Task GenericSort() {
      var documentItem = await CreateTextDocumentFromFileAsync("GenericSort.dfy");
      await _client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      Assert.IsTrue(Documents.TryGetDocument(documentItem.Uri, out var _));
    }
  }
}
