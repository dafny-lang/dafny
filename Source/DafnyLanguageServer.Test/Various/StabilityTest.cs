using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using OmniSharp.Extensions.LanguageServer.Protocol.Client;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.IO;
using System.Threading.Tasks;
using Xunit;
using Xunit.Abstractions;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Various {
  /// <summary>
  /// These integration tests involve various complex programs that are used
  /// to ensure that the language server is capable to load. It helps to ensure
  /// that for example syntax nodes are correctly visited.
  /// </summary>
  [Collection("Sequential Collection")] // Let slow tests run sequentially
  public class StabilityTest : DafnyLanguageServerTestBase, IAsyncLifetime {
    private const int MaxTestExecutionTimeMs = 60000;

    private ILanguageClient client;

    private async Task<TextDocumentItem> CreateTextDocumentFromFileAsync(string fileName) {
      var filePath = Path.Combine("Various", "TestFiles", fileName);
      var source = await File.ReadAllTextAsync(filePath, CancellationToken);
      return CreateTestDocument(source);
    }

    public async Task InitializeAsync() {
      client = await InitializeClient();
    }

    public Task DisposeAsync() {
      return Task.CompletedTask;
    }

    [Fact(Timeout = MaxTestExecutionTimeMs)]
    public async Task GhcMergeSort() {
      var documentItem = await CreateTextDocumentFromFileAsync("GHC-MergeSort.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      Assert.NotNull(await Documents.GetResolvedDocumentAsync(documentItem.Uri));
    }

    [Fact(Timeout = MaxTestExecutionTimeMs)]
    public async Task GenericSort() {
      var documentItem = await CreateTextDocumentFromFileAsync("GenericSort.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      Assert.NotNull(await Documents.GetResolvedDocumentAsync(documentItem.Uri));
    }

    [Fact(Timeout = MaxTestExecutionTimeMs)]
    public async Task StrongNestingDoesNotCauseStackOverlfow() {
      // Without a sufficiently large stack, the following code causes a stack overflow:
      // https://github.com/dafny-lang/dafny/issues/1447
      const string source = @"
method NestedExpression() {
  assert var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; var three := 3; true;
}";
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      Assert.NotNull(await Documents.GetResolvedDocumentAsync(documentItem.Uri));
    }

    public StabilityTest(ITestOutputHelper output) : base(output) {
    }
  }
}
