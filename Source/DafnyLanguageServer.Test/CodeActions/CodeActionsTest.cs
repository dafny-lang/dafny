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
  (>Insert explicit failing assertion->assert i + 1 != 0;
  <)var x := 2>< / (i + 1); 
}");
    }

    [Fact]
    public async Task ExplicitDivisionImp() {
      await TestCodeAction(@"
method Foo(b: bool, i: int, j: int)
{
  var x := b ==> (>Insert explicit failing assertion->assert i + 1 != 0;
                 <)2 ></ (i + 1) == j;
}");
    }

    [Fact]
    public async Task ExplicitDivisionImp2() {
      await TestCodeAction(@"
method Foo(b: bool, i: int, j: int)
{
  (>Insert explicit failing assertion->assert i + 1 != 0;
  <)var x := 2 ></ (i + 1) == j ==> b;
}");
    }

    [Fact]
    public async Task ExplicitDivisionAnd() {
      await TestCodeAction(@"
method Foo(b: bool, i: int, j: int)
{
  var x := b && (>Insert explicit failing assertion->assert i + 1 != 0;
                <)2 ></ (i + 1) == j;
}");
    }

    [Fact]
    public async Task ExplicitDivisionAnd2() {
      await TestCodeAction(@"
method Foo(b: bool, i: int, j: int)
{
  (>Insert explicit failing assertion->assert i + 1 != 0;
  <)var x := 2 ></ (i + 1) == j && b;
}");
    }


    [Fact]
    public async Task ExplicitDivisionOr() {
      await TestCodeAction(@"
method Foo(b: bool, i: int, j: int)
{
  var x := b || (>Insert explicit failing assertion->assert i + 1 != 0;
                <)2 ></ (i + 1) == j;
}");
    }

    [Fact]
    public async Task ExplicitDivisionOr2() {
      await TestCodeAction(@"
method Foo(b: bool, i: int, j: int)
{
  (>Insert explicit failing assertion->assert i + 1 != 0;
  <)var x := 2 ></ (i + 1) == j || b;
}");
    }



    [Fact]
    public async Task ExplicitDivisionAddParentheses() {
      await TestCodeAction(@"
method Foo(b: bool, i: int, j: int)
{
  (>Insert explicit failing assertion->assert (match b case true => i + 1 case false => i - 1) != 0;
  <)var x := 2 ></ match b case true => i + 1 case false => i - 1;
}");
    }

    [Fact]
    public async Task ExplicitDivisionExp() {
      await TestCodeAction(@"
method Foo(b: bool, i: int, j: int)
{
  (>Insert explicit failing assertion->assert i + 1 != 0;
  <)var x := b <== 2 ></ (i + 1) == j;
}");
    }

    [Fact]
    public async Task ExplicitDivisionExp2() {
      await TestCodeAction(@"
method Foo(b: bool, i: int, j: int)
{
  var x := (>Insert explicit failing assertion->(assert i + 1 != 0;
            2 / (i + 1) == j):::2 ></ (i + 1) == j<) <== b;
}");
    }

    [Fact]
    public async Task ExplicitDivisionByZeroFunction() {
      await TestCodeAction(@"
function Foo(i: int): int
{
  if i < 0 then
    (>Insert explicit failing assertion->assert i + 1 != 0;
    <)2>< / (i + 1)
  else
    2
}");
    }



    [Fact]
    public async Task ExplicitDivisionByZeroFunctionLetExpr() {
      await TestCodeAction(@"
function Foo(i: int): int
{
  match i {
    case _ =>
      (>Insert explicit failing assertion->assert i + 1 != 0;
      <)2>< / (i + 1)
  }
}");
    }

    // ParserError code action tests

    [Fact]
    public async Task CA_p_duplicate_modifier() {
      await TestCodeAction(@"
  abstract (>remove duplicate modifier->:::abstract <)module M {}
  ");
    }

    [Fact]
    public async Task CA_p_abstract_not_allowed() {
      await TestCodeAction(@"
  (>remove 'abstract'->:::abstract <)const c := 4
  ");
    }

    [Fact]
    public async Task CA_p_no_ghost_for_by_method() {
      await TestCodeAction(@"
  (>remove 'ghost'->:::ghost <)function f(): int
  {
    42
  } by method {
    return 42;
  }
  ");
    }

    [Fact]
    public async Task CA_p_ghost_forbidden_default() {
      await TestCodeAction(@"
  module {:options ""--function-syntax:3""} M {
    (>remove 'ghost'->:::ghost <)function f(): int { 42 }
  }
  ");
    }

    [Fact]
    public async Task CA_p_ghost_forbidden() {
      await TestCodeAction(@"
  (>remove 'ghost'->:::ghost <)module M {}
  ");
    }

    [Fact]
    public async Task CA_p_no_static() {
      await TestCodeAction(@"
  (>remove 'static'->:::static <)module M {}
  ");
    }

    [Fact]
    public async Task CA_p_no_opaque() {
      await TestCodeAction(@"
  (>remove 'opaque'->:::opaque <)module M {}
  ");
    }
    /*
        [Fact]
        public async Task CA_p_literal_string_required__1() {
          await TestCodeAction(@"
      module N { const opt := ""--function-syntax:4"" }
      import opened N
      module {:options (>remove 'opt'->:::opt<)} M{ }
      ");
        }

        [Fact]
        public async Task CA_p_literal_string_required__2() {
          await TestCodeAction(@"
      module N { const opt := ""--function-syntax:4"" }
      import opened N
      module {:options (>replace with empty string 'opt'->"""":::opt<)} M{ }
      ");
        }

        [Fact]
        public async Task CA_p_literal_string_required__3() {
          await TestCodeAction(@"
      module N { const opt := ""--function-syntax:4"" }
      import opened N
      module {:options (>enclose in quotes 'opt'->""opt"":::opt<)} M{ }
      ");
        }
    */
    [Fact]
    public async Task CA_p_no_leading_underscore__1() {
      await TestCodeAction(@"
  const (> remove underscore->myconst:::_myconst<) := 5
  ");
    }
    /*
        [Fact]
        public async Task CA_p_no_leading_underscore__2() {
          await TestCodeAction(@"
      function m(): ((>remove underscore->:::_<): int) {0}
      ");
        }
    */
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
              var modifiedOutput = string.Join("\n", ApplyEdits(textDocumentEdit, output)).Replace("\r\n", "\n");
              var expectedOutput = string.Join("\n", ApplySingleEdit(ToLines(output), expectedRange, expectedNewText)).Replace("\r\n", "\n");
              Assert.Equal(expectedOutput, modifiedOutput);
            }
          }
        }

        Assert.True(found,
          $"Did not find the code action '{expectedTitle}'. Available were:{string.Join(",", otherTitles)}");
      }
    }

    private static List<string> ApplyEdits(TextDocumentEdit textDocumentEdit, string output) {
      var inversedEdits = textDocumentEdit.Edits.ToList()
        .OrderByDescending(x => x.Range.Start.Line)
        .ThenByDescending(x => x.Range.Start.Character);
      var modifiedOutput = ToLines(output);
      foreach (var textEdit in inversedEdits) {
        modifiedOutput = ApplySingleEdit(modifiedOutput, textEdit.Range, textEdit.NewText);
      }

      return modifiedOutput;
    }

    private static List<string> ToLines(string output) {
      return output.ReplaceLineEndings("\n").Split("\n").ToList();
    }

    private static List<string> ApplySingleEdit(List<string> modifiedOutput, Range range, string newText) {
      var lineStart = modifiedOutput[range.Start.Line];
      var lineEnd = modifiedOutput[range.End.Line];
      modifiedOutput[range.Start.Line] =
        lineStart.Substring(0, range.Start.Character) + newText +
        lineEnd.Substring(range.End.Character);
      modifiedOutput = modifiedOutput.Take(range.Start.Line).Concat(
        modifiedOutput.Skip(range.End.Line)
      ).ToList();
      return modifiedOutput;
    }
  }
}
