#nullable enable
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using OmniSharp.Extensions.LanguageServer.Protocol.Client;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using Models = OmniSharp.Extensions.LanguageServer.Protocol.Models;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Immutable;
using System.Threading.Tasks;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.SemanticTokens;

[TestClass]
public class SemanticTokensTest : DafnyLanguageServerTestBase {
  private ILanguageClient? client;

  [TestInitialize]
  public async Task SetUp() {
    client = await InitializeClient();
  }

  private Task<Models.SemanticTokens?> RequestSemanticTokensFull(TextDocumentItem documentItem) {
    return client!.RequestSemanticTokensFull(
      new SemanticTokensParams {
        TextDocument = documentItem.Uri,
      },
      CancellationToken
    ).AsTask();
  }

  public async Task<ImmutableArray<int>> ParseAndCollectTokens(string source) {
    var documentItem = CreateTestDocument(source);
    await client!.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
    return (await RequestSemanticTokensFull(documentItem))!.Data;
  }

  [TestMethod]
  public async Task DocumentContainsSemanticTokens() {
    var blockCommentTokens =
      await ParseAndCollectTokens("/* C\nC\nC */ module A {}");
    var lineCommentTokens =
      await ParseAndCollectTokens("// A\nmodule A {}");
    var moduleNameTokens =
      await ParseAndCollectTokens("module M {}");
    var classNameTokens =
      await ParseAndCollectTokens("module M { class C {} }");
    var importNameTokens =
      await ParseAndCollectTokens("module M {} module N { import M' = M }");

    // FIXME
    // Assert.AreEqual("Y", classSymbol.Name);
    // Assert.AreEqual(new Range((0, 6), (9, 0)), classSymbol.Range);
    // Assert.AreEqual(SymbolKind.Class, classSymbol.Kind);
    // Assert.AreEqual(3, classChildren.Length);
  }
}
