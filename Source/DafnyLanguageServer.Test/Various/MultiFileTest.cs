using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using OmniSharp.Extensions.LanguageServer.Protocol.Client;
using System.IO;
using System.Linq;
using System.Threading.Tasks;
using Xunit;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Various {

  public class MultiFileTest : DafnyLanguageServerTestBase, IAsyncLifetime {
    private static readonly string TestFilePath = Path.Combine(Directory.GetCurrentDirectory(), "Various", "TestFiles", "testFile.dfy");

    private ILanguageClient client;

    public async Task InitializeAsync() {
      client = await InitializeClient();
    }

    public Task DisposeAsync() {
      return Task.CompletedTask;
    }

    // https://github.com/dafny-lang/language-server-csharp/issues/40
    [Fact]
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
      Assert.NotNull(document);
      Assert.True(!document.Diagnostics.Any());
    }

    // https://github.com/dafny-lang/language-server-csharp/issues/40
    [Fact]
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
      Assert.NotNull(document);
      Assert.Single(document.Diagnostics);
    }
  }
}
