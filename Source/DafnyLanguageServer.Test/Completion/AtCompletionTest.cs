using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;
using System.Linq;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Xunit;
using Xunit.Abstractions;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Completion {
  public class AtCompletionTest : ClientBasedLanguageServerTest {

    private async Task<List<CompletionItem>> RequestCompletionAsync(TextDocumentItem documentItem, Position position) {
      var completionList = await client.RequestCompletion(
        new CompletionParams {
          TextDocument = documentItem.Uri,
          Position = position
        },
        CancellationToken
      ).AsTask();
      return completionList.OrderBy(completion => completion.Label).ToList();
    }

    [Fact]
    public async Task CompleteNoAtAttributeDuringAtCall() {
      var source = @"
method Foo() { label start: previous@(x); }".TrimStart();
      var documentItem = CreateAndOpenTestDocument(source, "CompleteAtCall.dfy");

      var completionList = await RequestCompletionAsync(documentItem, (0, 37));
      Assert.Empty(completionList);
    }

    private static void AssertEqualToAllCompletions(List<CompletionItem> completionList) {
      Assert.Equal(Attributes.BuiltinAtAttributes.Count, completionList.Count);
      for (var i = 0; i < completionList.Count; i++) {
        Assert.Equal(Attributes.BuiltinAtAttributes[0].Name, completionList[0].Label);
        Assert.Equal(CompletionItemKind.Constructor, completionList[1].Kind);
      }
    }

    [Fact]
    public async Task CompleteAtAttributeAtBeginningOfFile() {
      var source = "@";
      var documentItem = CreateTestDocument(source, "CompleteAt.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var completionList = await RequestCompletionAsync(documentItem, (0, 1));
      AssertEqualToAllCompletions(completionList);
    }

    [Fact]
    public async Task CompleteAtAttributeBeforeMethod() {
      var source = @"
/* Does what is expected */ @ method Foo() { }".TrimStart();
      var documentItem = CreateTestDocument(source, "CompleteAtBeforeMethod.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var completionList = await RequestCompletionAsync(documentItem, (0, 29));
      AssertEqualToAllCompletions(completionList);
    }

    [Fact]
    public async Task CompleteAtAttributeBeforeMethodAfterNewline() {
      var source = @"
/* Does what is expected */".TrimStart() + "\n" +
"@ method Foo() { }".TrimStart();
      var documentItem = CreateTestDocument(source, "CompleteOnThisReturnsClassMembers.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var completionList = await RequestCompletionAsync(documentItem, (1, 1));
      AssertEqualToAllCompletions(completionList);
    }

    public AtCompletionTest(ITestOutputHelper output) : base(output) {
    }
  }
}
