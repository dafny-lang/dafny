#nullable enable
using System.Collections.Generic;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using OmniSharp.Extensions.LanguageServer.Protocol.Client;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using Models = OmniSharp.Extensions.LanguageServer.Protocol.Models;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Immutable;
using System.Threading.Tasks;
using Xunit;
using Xunit.Abstractions;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.SemanticTokens;

public class SemanticTokensTest : DafnyLanguageServerTestBase {
  private ILanguageClient? client;

  public SemanticTokensTest(ITestOutputHelper output) : base(output) {
  }

  private Task<Models.SemanticTokens?> RequestSemanticTokensFull(TextDocumentItem documentItem) {
    return client!.RequestSemanticTokensFull(
      new SemanticTokensParams {
        TextDocument = documentItem.Uri,
      },
      CancellationToken
    ).AsTask();
  }

  public record SerializedToken(int Line, int Col, int Length, int Type, int Mods);

  public async Task<List<SerializedToken>> ParseAndCollectTokens(string source) {
    var documentItem = CreateTestDocument(source);
    await client!.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
    var data = (await RequestSemanticTokensFull(documentItem))!.Data;
    return ParseData(data);
  }

  private List<SerializedToken> ParseData(ImmutableArray<int> data) {
    var currentLine = 0;
    var currentCol = 0;
    var tokens = new List<SerializedToken>();
    for (var i = 0; i < data.Length; i += 5) {
      currentLine += data[i];
      if (data[i] > 0) {
        currentCol = data[i + 1];
      } else {
        currentCol += data[i + 1];
      }

      var length = data[i + 2];
      var type = data[i + 3];
      var mods = data[i + 4];
      tokens.Add(new SerializedToken(currentLine, currentCol, length, type, mods));
    }

    return tokens;
  }

  [Fact]
  public async Task DocumentContainsSemanticTokens() {
    client = await InitializeClient();
    var blockCommentTokens =
      await ParseAndCollectTokens("/* C\nC\nC */ module A {}");
    Assert.Equal(3, blockCommentTokens.Count);
    Assert.Equal(new SerializedToken(0, 0, 11, 0, 0), blockCommentTokens[0]);

    var moduleNameTokens =
      await ParseAndCollectTokens("module M {}");
    Assert.Equal(2, moduleNameTokens.Count);
    Assert.Equal(new SerializedToken(0, 0, 6, 1, 2), moduleNameTokens[0]);
    Assert.Equal(new SerializedToken(0, 7, 1, 6, 0), moduleNameTokens[1]);

    var lineCommentTokens =
      await ParseAndCollectTokens("// A\nmodule A {}");

    Assert.Equal(3, lineCommentTokens.Count);
    Assert.Equal(new SerializedToken(0, 0, 4, 0, 0), lineCommentTokens[0]);

    var classNameTokens =
      await ParseAndCollectTokens("module M { class C {} }");

    // Our backend emits semantic tokens first by looking at bare tokens (module, class)
    // and then names (M, C)
    Assert.Equal(4, classNameTokens.Count);
    Assert.Equal(new SerializedToken(0, 11, 5, 1, 2), classNameTokens[1]);
    Assert.Equal(new SerializedToken(0, 17, 1, 9, 2), classNameTokens[3]);

    // Just to ensure no crash
    var importNameTokens =
      await ParseAndCollectTokens("module M {} module N { import M' = M } /* test */");
    Assert.Equal(8, importNameTokens.Count);

  }
}
