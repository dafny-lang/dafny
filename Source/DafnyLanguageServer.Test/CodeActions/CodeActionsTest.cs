using System;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;
using System.Linq;
using System.Text.RegularExpressions;
using System.Threading.Tasks;
using Castle.Core.Internal;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Xunit;
using Xunit.Abstractions;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

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
    public async Task MethodKeywordCodeAction() {
      await SetUp(o => o.Set(CommonOptionBag.RelaxDefiniteAssignment, true));

      MarkupTestFile.GetPositionsAndAnnotatedRanges(@"
method><".TrimStart(), out var source, out var positions,
        out var ranges);
      var documentItem = await CreateOpenAndWaitForResolve(source);
      var position = positions[0];
      var completionList = await RequestCodeActionAsync(documentItem, new Range(position, position));
      Assert.Empty(completionList);
    }

    [Fact]
    public async Task TypeTestCodeAction() {
      await SetUp(o => o.Set(CommonOptionBag.RelaxDefiniteAssignment, true));

      MarkupTestFile.GetPositionsAndAnnotatedRanges(@"module M {
  trait Object {
   ghost function typeId() : (id: string)
  }

  type A extends Object {
   ghost function typeId() : (id: string)  { ""A"" }
  }

  type B extends Object {
   ghost function typeId() : (id: string)  { ""B"" }
  }
  type C extends Object {
   ghost function typeId() : (id: string)  { ""C"" }
  }

  lemma test(x: Object)
    ensures multiset{x is A, x is B, x is C}[true] == 1
  {
    var _ := x.typeId();
    if (x is A) {
      assert x !is B.><
    }
  }
}".TrimStart(), out var source, out var positions,
        out var ranges);
      var documentItem = await CreateOpenAndWaitForResolve(source);
      var position = positions[0];
      var completionList = await RequestCodeActionAsync(documentItem, new Range(position, position));
      Assert.Empty(completionList);
    }

    [Fact]
    public async Task TestAssertFalseNotSuggestingItself() {
      await TestNoCodeAction(@"
method NoCodeAction() {
  assert fal><se;
}");
    }

    [Fact]
    public async Task TestEnsureFalseNotSuggestingItself() {
      await TestNoCodeAction(@"
method NoCodeAction() ensures f><alse {
}", excepted: message => message == "Assert postcondition at return location where it fails");
    }

    [Fact]
    public async Task TestInsertion() {
      await TestCodeAction(@"
datatype L = N | C(t: L)

method Dec(c: L)
  decreases c, 1, 1
{(>Insert explicit failing assertion->
  assert (old(c), old(1) decreases to c, 1);<)
  Da><c(c);
}
method Dac(c: L) 
  decreases c, 1 {
    Dec(c);
}");
    }

    [Fact]
    public async Task TestCalcIntroduction() {
      await TestCodeAction(@"
method Test() {
  assert 1 =><= 2(>Insert a calc statement-> by {
    calc {
      1;
      2;
    }
  }:::;<)
}");
    }

    [Fact]
    public async Task TestCalcIntroductionEquiv() {
      await TestCodeAction(@"
method Test() {
  assert true <=><=> false(>Insert a calc statement-> by {
    calc <==> {
      true;
      false;
    }
  }:::;<)
}");
    }

    [Fact]
    public async Task TestForallIntroduction() {
      await TestCodeAction(@"
method Test() {
  assert for><all i | i % 4 == 1 :: i % 2 == 0(>Insert a forall statement-> by {
    forall i: int | i % 4 == 1 ensures i % 2 == 0 {
      assert i % 2 == 0;
    }
  }:::;<)
}");
    }

    [Fact]
    public async Task TestForallIntroductionFunction() {
      await TestCodeAction(@"
function Test(): int {
  assert for><all i | i % 4 == 1 :: i % 2 == 0(>Insert a forall statement-> by {
    forall i: int | i % 4 == 1 ensures i % 2 == 0 {
      assert i % 2 == 0;
    }
  }:::;<)
  1
}");
    }

    [Fact]
    public async Task GitIssue4401CorrectInsertionPlace() {
      await TestCodeAction(@"
predicate P(i: int)

method Test() {
  var x :><| P(x)(>Insert explicit failing assertion-> by {
    assert exists x: int :: P(x);
  }:::;<)
}");
    }

    [Fact]
    public async Task InsertIntoByStatement() {
      await TestCodeAction(@"
predicate P(i: int)

function Test(i: int): int
  requires P(i) {
  i
}

method TestMethod() {
  assert Test><(1) == 1 by {
    (>Insert explicit failing assertion->assert P(1);
    <)calc {
      1;
      1;
    }
  }
}");
    }

    [Fact]
    public async Task InsertIntoEmptyByStatement() {
      await TestCodeAction(@"
predicate P(i: int)

function Test(i: int): int
  requires P(i) {
  i
}

method TestMethod() {
  assert Test><(1) == 1 by {
  (>Insert explicit failing assertion->  assert P(1);
  <)}
}");
    }

    [Fact]
    public async Task GitIssue4401CorrectInsertionPlaceModule() {
      await TestCodeAction(@"
module Test {
  class TheTest {
    predicate P(i: int)

    method Test() {
      var x :><| P(x)(>Insert explicit failing assertion-> by {
        assert exists x: int :: P(x);
      }:::;<)
    }
  }
}");
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
    i := 11;
  }
}");
    }

    [Fact]
    public async Task CodeActionSuggestsInliningPostConditionWithExtraIndentation() {
      await TestCodeAction(@"
const x := 1
  method f() returns (i: int)
    ensures i > 10 ><{
  (>Assert postcondition at return location where it fails->  assert i > 10;
  <)}");
    }

    [Fact]
    public async Task CodeActionSuggestsInliningPostConditionWithExtraTabIndentation() {
      var t = "\t";
      await TestCodeAction($@"
const x := 1
  method f() returns (i: int)
{t}{t}{t}{t}{t}{t}ensures i > 10 ><{{
{t}{t}{t}(>Assert postcondition at return location where it fails->{t}assert i > 10;
{t}{t}{t}<)}}");
    }

    [Fact]
    public async Task CodeActionSuggestsInliningPostConditionWithExtraIndentation2() {
      await TestCodeAction(@"
const x := 1
  method f() returns (i: int)
    ensures i > 10
><{
(>Assert postcondition at return location where it fails->  assert i > 10;
<)}");
    }

    [Fact]
    public async Task CodeActionSuggestsInliningPostConditionWithExtraIndentation2bis() {
      await TestCodeAction(@"
const x := 1
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
const x := 1
  method f() returns (i: int)
    ensures i > 10
  ><{(>Assert postcondition at return location where it fails-> assert i > 10;
  <)}");
    }

    [Fact]
    public async Task CodeActionSuggestsInliningPostConditionWithExtraIndentation3() {
      await TestCodeAction(@"
const x := 1
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
    public async Task ExplicitNestedIdentifier() {
      await TestCodeAction(@"
datatype D = C(value: int) | N

function Test(e: D, inputs: map<int, int>): bool {
  match e
  case N => true
  case C(index) => (>Insert explicit failing assertion->assert index in inputs;
                   <)inputs><[index] == index // Here
}");
    }

    [Fact]
    public async Task ExplicitDivisionByZeroFunction() {
      await TestCodeAction(@"
function Foo(i: int): int
{
  (>Insert explicit failing assertion->assert i + 1 != 0;
  <)var x := 2>< / (i + 1); 
  x
}");
    }

    [Fact]
    public async Task ExplicitDivisionByZeroMethod() {
      await TestCodeAction(@"
method Foo(i: int)
{
  var x := 2>< / (i + 1)(>Insert explicit failing assertion-> by {
    assert i + 1 != 0;
  }:::;<)
}");
    }

    [Fact]
    public async Task ExplicitDivisionImpFunction() {
      await TestCodeAction(@"
function Foo(b: bool, i: int, j: int): bool
{
  var x := b ==> (>Insert explicit failing assertion->assert i + 1 != 0;
                 <)2 ></ (i + 1) == j;
  x
}");
    }

    [Fact]
    public async Task ExplicitDivisionImpImpMethod() {
      await TestCodeAction(@"
method Foo(b: bool, i: int, j: int)
{
  var x := b ==> b ==> (>Insert explicit failing assertion->assert i + 1 != 0;
                       <)2 ></ (i + 1) == j;
}");
    }

    [Fact]
    public async Task ExplicitDivisionImpMethod() {
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
  var x := 2 ></ (i + 1) == j ==> b(>Insert explicit failing assertion-> by {
    assert i + 1 != 0;
  }:::;<)
}");
    }

    [Fact]
    public async Task ExplicitDivisionAndFunction() {
      await TestCodeAction(@"
function Foo(b: bool, i: int, j: int): bool
{
  var x := b && (>Insert explicit failing assertion->assert i + 1 != 0;
                <)2 ></ (i + 1) == j;
  x
}");
    }


    [Fact]
    public async Task ExplicitDivisionAndMethod() {
      await TestCodeAction(@"
method Foo(b: bool, i: int, j: int)
{
  var x := b && (>Insert explicit failing assertion->assert i + 1 != 0;
                <)2 ></ (i + 1) == j;
}");
    }

    [Fact]
    public async Task ExplicitDivisionAnd2Function() {
      await TestCodeAction(@"
function Foo(b: bool, i: int, j: int): bool
{
  (>Insert explicit failing assertion->assert i + 1 != 0;
  <)var x := 2 ></ (i + 1) == j && b;
  x
}");
    }

    [Fact]
    public async Task ExplicitDivisionAnd2Method() {
      await TestCodeAction(@"
method Foo(b: bool, i: int, j: int)
{
  var x := 2 ></ (i + 1) == j && b(>Insert explicit failing assertion-> by {
    assert i + 1 != 0;
  }:::;<)
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
  var x := 2 ></ (i + 1) == j || b(>Insert explicit failing assertion-> by {
    assert i + 1 != 0;
  }:::;<)
}");
    }

    [Fact]
    public async Task ExplicitDivisionAddParentheses() {
      await TestCodeAction(@"
method Foo(b: bool, i: int, j: int)
{
  var x := 2 ></ match b case true => i + 1 case false => i - 1(>Insert explicit failing assertion-> by {
    assert (match b case true => i + 1 case false => i - 1) != 0;
  }:::;<)
}");
    }

    [Fact]
    public async Task ExplicitDivisionAddParentheses2() {
      await TestCodeAction(@"
function Foo(b: bool, i: int, j: int): int
{
  (>Insert explicit failing assertion->assert (match b case true => i + 1 case false => i - 1) != 0;
  <)var x := 2 ></ match b case true => i + 1 case false => i - 1;
  x
}");
    }

    [Fact]
    public async Task ExplicitDivisionExpMethod() {
      await TestCodeAction(@"
method Foo(b: bool, i: int, j: int)
{
  var x := b <== 2 ></ (i + 1) == j(>Insert explicit failing assertion-> by {
    assert i + 1 != 0;
  }:::;<)
}");
    }

    [Fact]
    public async Task ExplicitDivisionExpFunction() {
      await TestCodeAction(@"
function Foo(b: bool, i: int, j: int): int
{
  (>Insert explicit failing assertion->assert i + 1 != 0;
  <)var x := b <== 2 ></ (i + 1) == j;
  2
}");
    }

    [Fact]
    public async Task ExplicitDivisionExp2Function() {
      await TestCodeAction(@"
function Foo(b: bool, i: int, j: int): bool
{
  var x := (>Insert explicit failing assertion->(assert i + 1 != 0;
            2 / (i + 1) == j):::2 ></ (i + 1) == j<) <== b;
  x
}");
    }

    [Fact]
    public async Task ExplicitDivisionExp2Method() {
      await TestCodeAction(@"
method Foo(b: bool, i: int, j: int)
{
  var x := (>Insert explicit failing assertion->(assert i + 1 != 0;
            2 / (i + 1) == j):::2 ></ (i + 1) == j<) <== b;
}");
    }

    [Fact]
    public async Task ExplicitDivisionByZeroIfFunction() {
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
    public async Task ExplicitDivisionByZeroMatchFunctionLetExpr() {
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

    private static readonly Regex NewlineRegex = new Regex("\r?\n");

    private async Task TestNoCodeAction(string source, Func<string, bool> excepted = null) {
      await SetUp(o => o.Set(CommonOptionBag.RelaxDefiniteAssignment, true));
      MarkupTestFile.GetPositionsAndAnnotatedRanges(source.TrimStart(), out var output, out var positions,
        out var ranges);
      var documentItem = await CreateOpenAndWaitForResolve(output);
      var diagnostics = await GetLastDiagnostics(documentItem);
      Assert.Equal(0, ranges.Count);
      foreach (var position in positions) {
        var completionList = await RequestCodeActionAsync(documentItem, new Range(position, position));
        completionList = excepted == null
          ? completionList
          : completionList.Where(completion =>
            completion.CodeAction is not { Title: var title } || !excepted(title)).ToList();
        Assert.Empty(completionList);
      }
    }

    private async Task TestCodeAction(string source) {
      await SetUp(o => o.Set(CommonOptionBag.RelaxDefiniteAssignment, true));

      MarkupTestFile.GetPositionsAndAnnotatedRanges(source.TrimStart(), out var output, out var positions,
        out var ranges);
      var documentItem = await CreateOpenAndWaitForResolve(output);
      var diagnostics = await GetLastDiagnostics(documentItem);
      if (ranges.Count != diagnostics.Length) {
        Assert.True(ranges.Count == diagnostics.Length, string.Join("\n", diagnostics.Select(d => d.ToString())));
      }

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
              var modifiedOutput = DocumentEdits.ApplyEdits(textDocumentEdit, output);
              var expectedOutput =
                DocumentEdits.ApplyEdit(DocumentEdits.ToLines(output), expectedRange, expectedNewText);
              Assert.Equal(expectedOutput, modifiedOutput);
            }
          }
        }

        if (otherTitles.IsNullOrEmpty()) {
          // Parsing gone wrong, we display diagnostics
          Assert.True(false, output + "\n" + string.Join("\n", diagnostics.Select(d => d.ToString())));
        } else {
          Assert.True(found,
            $"Did not find the code action '{expectedTitle}'. Available were:{string.Join(",", otherTitles)}");
        }
      }
    }

    public CodeActionTest(ITestOutputHelper output) : base(output) {
    }
  }
}
