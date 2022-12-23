using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Collections.Generic;
using System.Linq;
using System.Text.RegularExpressions;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.CodeActions {
  [TestClass]
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

    [TestMethod]
    public async Task CodeActionSuggestsInliningPostCondition() {
      await TestCodeActionHelper(@"
method f() returns (i: int)
  ensures i > 10 >>>{
[[Assert postcondition at return location where it fails|  assert i > 10;
]]}");
    }

    [TestMethod]
    public async Task CodeActionSuggestsInliningPostConditionInIfStatement() {
      await TestCodeActionHelper(@"
method f(b: bool) returns (i: int)
  ensures i > 10 {
  if b >>>{
    i := 0;
  [[Assert postcondition at return location where it fails|  assert i > 10;
  ]]} else {
    i := 10;
  }
}");
    }


    [TestMethod]
    public async Task CodeActionSuggestsInliningPostConditionWithExtraIndentation() {
      await TestCodeActionHelper(@"
const x := 1;
  method f() returns (i: int)
    ensures i > 10 >>>{
  [[Assert postcondition at return location where it fails|  assert i > 10;
  ]]}");
    }

    [TestMethod]
    public async Task CodeActionSuggestsInliningPostConditionWithExtraTabIndentation() {
      var t = "\t";
      await TestCodeActionHelper($@"
const x := 1;
  method f() returns (i: int)
{t}{t}{t}{t}{t}{t}ensures i > 10 >>>{{
{t}{t}{t}[[Assert postcondition at return location where it fails|{t}assert i > 10;
{t}{t}{t}]]}}");
    }

    [TestMethod]
    public async Task CodeActionSuggestsInliningPostConditionWithExtraIndentation2() {
      await TestCodeActionHelper(@"
const x := 1;
  method f() returns (i: int)
    ensures i > 10
>>>{
[[Assert postcondition at return location where it fails|  assert i > 10;
]]}");
    }

    [TestMethod]
    public async Task CodeActionSuggestsInliningPostConditionWithExtraIndentation2bis() {
      await TestCodeActionHelper(@"
const x := 1;
  method f() returns (i: int)
    ensures i > 10
>>>{
    assert 1 == 1; /* a commented { that should not prevent indentation to be 4 */
[[Assert postcondition at return location where it fails|    assert i > 10;
]]}");
    }


    [TestMethod]
    public async Task CodeActionSuggestsInliningPostConditionWithExtraIndentation2C() {
      await TestCodeActionHelper(@"
const x := 1;
  method f() returns (i: int)
    ensures i > 10
  >>>{[[Assert postcondition at return location where it fails| assert i > 10;
  ]]}");
    }

    [TestMethod]
    public async Task CodeActionSuggestsInliningPostConditionWithExtraIndentation3() {
      await TestCodeActionHelper(@"
const x := 1;
  method f() returns (i: int)
    ensures i > 10
  >>>{
  [[Assert postcondition at return location where it fails|  assert i > 10;
  ]]}");
    }

    private async Task TestCodeActionHelper(string source) {
      source = source.TrimStart();
      var extractCodeAction =
        new Regex(@"(?<newline>(?=\n))|>>>(?<position>(?=.))|\[\[(?<message>.*)\|(?<inserted>[\s\S]*?)\]\]");
      var matches = extractCodeAction.Matches(source);
      var initialCode = "";
      var lastPosition = 0;
      var lastStartOfLine = 0;
      string expectedDafnyCodeActionTitle = null;
      string expectedDafnyCodeActionCode = null;
      Range requestPosition = null;
      Range expectedDafnyCodeActionRange = null;
      var numberOfLines = 0;
      var positionOffset = 0;
      for (var i = 0; i < matches.Count; i++) {
        var match = matches[i];
        initialCode += source.Substring(lastPosition, match.Index - lastPosition);
        if (match.Groups["message"].Success) {
          expectedDafnyCodeActionTitle = match.Groups["message"].Value;
          expectedDafnyCodeActionCode = match.Groups["inserted"].Value;
          Position position = (numberOfLines, (match.Index + positionOffset) - lastStartOfLine);
          expectedDafnyCodeActionRange = (position, position);
          positionOffset -= match.Value.Length;
        }

        if (match.Groups["position"].Success) {
          Position position = (numberOfLines, (match.Index + positionOffset) - lastStartOfLine);
          requestPosition = (position, position);
          positionOffset -= match.Value.Length;
        }

        if (match.Groups["newline"].Success) {
          lastStartOfLine = match.Index + positionOffset + 1;
          numberOfLines++;
        }

        lastPosition = match.Index + match.Value.Length;
      }

      initialCode += source.Substring(lastPosition);

      Assert.IsNotNull(expectedDafnyCodeActionCode, "Could not find an expected quick fix code");
      Assert.IsNotNull(expectedDafnyCodeActionTitle, "Could not find an expected quick fix title");
      Assert.IsNotNull(expectedDafnyCodeActionRange, "Could not find an expected quick fix range");

      await TestIfCodeAction(initialCode, requestPosition, expectedDafnyCodeActionTitle, expectedDafnyCodeActionCode,
        expectedDafnyCodeActionRange);
    }

    private static Regex NewlineRegex = new Regex("\r?\n");

    private async Task TestIfCodeAction(string source, Range requestPosition, string expectedDafnyCodeActionTitle, string expectedDafnyCodeAction,
      Range expectedDafnyCodeActionRange) {
      await SetUp(o => o.Set(CommonOptionBag.RelaxDefiniteAssignment, true));
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var verificationDiagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken);
      if (0 == verificationDiagnostics.Length) {
        verificationDiagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken);
      }
      Assert.AreEqual(1, verificationDiagnostics.Length);

      var completionList = await RequestCodeActionAsync(documentItem, requestPosition);
      var found = false;
      var otherTitles = new List<string>();
      foreach (var completion in completionList) {
        if (completion.CodeAction is { Title: var title } codeAction) {
          otherTitles.Add(title);
          if (title == expectedDafnyCodeActionTitle) {
            found = true;
            codeAction = await RequestResolveCodeAction(codeAction);
            var textDocumentEdit = codeAction.Edit?.DocumentChanges?.Single().TextDocumentEdit;
            Assert.IsNotNull(textDocumentEdit);
            var edit = textDocumentEdit.Edits.Single();
            Assert.AreEqual(NewlineRegex.Replace(expectedDafnyCodeAction, "\n"), NewlineRegex.Replace(edit.NewText, "\n"));
            Assert.AreEqual(expectedDafnyCodeActionRange, edit.Range);
          }
        }
      }

      Assert.IsTrue(found,
        $"Did not find the code action '{expectedDafnyCodeActionTitle}'. Available were:{string.Join(",", otherTitles)}");
    }
  }
}
