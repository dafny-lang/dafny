using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;
using System.Linq;
using System.Text.RegularExpressions;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Xunit;
using XunitAssertMessages;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.CodeActions {
  public class CodeActionTest : ClientBasedLanguageServerTest {

    [Fact]
    public async Task RemoveDuplicateModifier() {
      await TestErrorCodeAction(@"
abstract (>remove 'abstract'->:::abstract <)module Foo {
}");
    }

    [Fact]
    public async Task RemoveAbstractFromClass() {
      await TestErrorCodeAction(@"
(>remove 'abstract'->:::abstract <)class Foo {
}");
    }

    [Fact]
    public async Task RemoveLeadingUnderscore() {
      await TestErrorCodeAction(@"
method Foo()
{
  var (>remove underscore->qx:::_x<) := 3; 
}");
    }





    private static readonly Regex NewlineRegex = new Regex("\r?\n");

    private async Task<List<CommandOrCodeAction>> RequestTestCodeActionAsync(TextDocumentItem documentItem, Range range) {
      var completionList = await client.RequestCodeAction(
        new CodeActionParams {
          TextDocument = documentItem.Uri.GetFileSystemPath(),
          Range = range
        },
        CancellationToken
      ).AsTask();
      return completionList.ToList();
    }

    private async Task<CodeAction> RequestResolveTestCodeAction(CodeAction codeAction) {
      return await client.ResolveCodeAction(codeAction, CancellationToken);
    }
    private async Task TestErrorCodeAction(string source) { // Same as CodeActionsTest.TestCodeAction
      await SetUp(o => o.Set(CommonOptionBag.RelaxDefiniteAssignment, true));

      MarkupTestFile.GetPositionsAndAnnotatedRanges(source.TrimStart(), out var output, out var positions,
        out var ranges);
      var documentItem = CreateTestDocument(output);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var diagnostics = await GetLastDiagnostics(documentItem, CancellationToken);
      Assert.Equal(ranges.Count, diagnostics.Length);

      if (positions.Count != ranges.Count) {
        positions = ranges.Select(r => r.Range.Start).ToList();
      }

      foreach (var actionData in positions.Zip(ranges)) {
        var position = actionData.First;
        var split = actionData.Second.Annotation.Split("->");
        var expectedTitle = split[0];
        var expectedNewText = split.Length > 1 ? split[1] : "";
        var expectedRange = actionData.Second.Range;
        var completionList = await RequestTestCodeActionAsync(documentItem, new Range(position, position));
        var found = false;
        var otherTitles = new List<string>();
        foreach (var completion in completionList) {
          if (completion.CodeAction is { Title: var title } codeAction) {
            otherTitles.Add(title);
            if (title == expectedTitle) {
              found = true;
              codeAction = await RequestResolveTestCodeAction(codeAction);
              var textDocumentEdit = codeAction.Edit?.DocumentChanges?.Single().TextDocumentEdit;
              Assert.NotNull(textDocumentEdit);
              var edit = textDocumentEdit.Edits.Single();
              Assert.Equal(
                NewlineRegex.Replace(expectedNewText, "\n"),
                NewlineRegex.Replace(edit.NewText, "\n"));
              Assert.Equal(expectedRange, edit.Range);
            }
          }
        }

        Assert.True(found,
          $"Did not find the code action '{expectedTitle}'. Available were:{string.Join(",", otherTitles)}");
      }
    }
  }
}
