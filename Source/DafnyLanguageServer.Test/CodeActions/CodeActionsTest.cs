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
    private async Task<List<CommandOrCodeAction>> RequestCodeActionAsync(TextDocumentItem documentItem, Range range) {
      var completionList = await client.RequestCodeAction(
        new CodeActionParams {
          TextDocument = documentItem.Uri.GetFileSystemPath(),
          Range = range
        },
        CancellationToken
      ).AsTask();
      return completionList.ToList();
    }

    private async Task<CodeAction> RequestResolveCodeAction(CodeAction codeAction) {
      return await client.ResolveCodeAction(codeAction, CancellationToken);
    }

    [Fact]
    public async Task CodeActionSuggestsRemovingUnderscore() {
      await TestCodeAction(@"
method Foo()
{
  var (>remove underscore->x:::_x<) := 3; 
}");
    }

    [Fact]
    public async Task CodeActionSuggestsInliningPostCondition() {
      await TestCodeAction(@"
method f() returns (i: int)
  ensures i > 10 ><{
  i := 3;
(>Assert postcondition at return location where it fails->  assert i > 10;
<)}");
    }

    [Fact]
    public async Task CodeActionSuggestsInliningPostConditionInIfStatement() {
      await TestCodeAction(@"
method f(b: bool) returns (i: int)
  ensures i > 10 {
  if b ><{
    i := 0;
  (>Assert postcondition at return location where it fails->  assert i > 10;
  <)} else {
    i := 10;
  }
}");
    }

    [Fact]
    public async Task CodeActionSuggestsInliningPostConditionWithExtraIndentation() {
      await TestCodeAction(@"
const x := 1;
  method f() returns (i: int)
    ensures i > 10 ><{
  (>Assert postcondition at return location where it fails->  assert i > 10;
  <)}");
    }

    [Fact]
    public async Task CodeActionSuggestsInliningPostConditionWithExtraTabIndentation() {
      var t = "\t";
      await TestCodeAction($@"
const x := 1;
  method f() returns (i: int)
{t}{t}{t}{t}{t}{t}ensures i > 10 ><{{
{t}{t}{t}(>Assert postcondition at return location where it fails->{t}assert i > 10;
{t}{t}{t}<)}}");
    }

    [Fact]
    public async Task CodeActionSuggestsInliningPostConditionWithExtraIndentation2() {
      await TestCodeAction(@"
const x := 1;
  method f() returns (i: int)
    ensures i > 10
><{
(>Assert postcondition at return location where it fails->  assert i > 10;
<)}");
    }

    [Fact]
    public async Task CodeActionSuggestsInliningPostConditionWithExtraIndentation2bis() {
      await TestCodeAction(@"
const x := 1;
  method f() returns (i: int)
    ensures i > 10
><{
    assert 1 == 1; /* a commented { that should not prevent indentation to be 4 */
(>Assert postcondition at return location where it fails->    assert i > 10;
<)}");
    }


    [Fact]
    public async Task CodeActionSuggestsInliningPostConditionWithExtraIndentation2C() {
      await TestCodeAction(@"
const x := 1;
  method f() returns (i: int)
    ensures i > 10
  ><{(>Assert postcondition at return location where it fails-> assert i > 10;
  <)}");
    }

    [Fact]
    public async Task CodeActionSuggestsInliningPostConditionWithExtraIndentation3() {
      await TestCodeAction(@"
const x := 1;
  method f() returns (i: int)
    ensures i > 10
  ><{
  (>Assert postcondition at return location where it fails->  assert i > 10;
  <)}");
    }

    [Fact]
    public async Task RemoveAbstractFromClass() {
      await TestCodeAction(@"
(>remove 'abstract'->:::abstract <)class Foo {
}");
    }

    [Fact]
    public async Task ExplicitDivisionByZero() {
      await TestCodeAction(@"
method Foo(i: int)
{
  (>Explicit failing assertion->assert i + 1 != 0;
  <)var x := 2>< / (i + 1); 
}");
    }

    private static readonly Regex NewlineRegex = new Regex("\r?\n");

    private async Task TestCodeAction(string source) {
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
        var completionList = await RequestCodeActionAsync(documentItem, new Range(position, position));
        var found = false;
        var otherTitles = new List<string>();
        foreach (var completion in completionList) {
          if (completion.CodeAction is { Title: var title } codeAction) {
            otherTitles.Add(title);
            if (title == expectedTitle) {
              found = true;
              codeAction = await RequestResolveCodeAction(codeAction);
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
