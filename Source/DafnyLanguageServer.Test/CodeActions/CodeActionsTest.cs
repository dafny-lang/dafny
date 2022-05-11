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
[[Explicit the failing assert|  assert i > 10;
]]}");
    }

    [TestMethod]
    public async Task CodeActionSuggestsInliningPostConditionInIfStatement() {
      await TestCodeActionHelper(@"
method f(b: bool) returns (i: int)
  ensures i > 10 {
  if b >>>{
    i := 0;
  [[Explicit the failing assert|  assert i > 10;
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
  [[Explicit the failing assert|  assert i > 10;
  ]]}");
    }

    [TestMethod]
    public async Task CodeActionSuggestsInliningPostConditionWithExtraTabIndentation() {
      var t = "\t\t\t";
      await TestCodeActionHelper($@"
const x := 1;
  method f() returns (i: int)
{t}{t}ensures i > 10 >>>{{
{t}[[Explicit the failing assert|{t}assert i > 10;
{t}]]}}");
    }


    [TestMethod]
    public async Task CodeActionSuggestsInliningPostConditionWithExtraIndentation2() {
      await TestCodeActionHelper(@"
const x := 1;
  method f() returns (i: int)
    ensures i > 10
>>>{
[[Explicit the failing assert|  assert i > 10;
]]}");
    }


    [TestMethod]
    public async Task CodeActionSuggestsInliningPostConditionWithExtraIndentation3() {
      await TestCodeActionHelper(@"
const x := 1;
  method f() returns (i: int)
    ensures i > 10
  >>>{
  [[Explicit the failing assert|  assert i > 10;
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
      string expectedQuickFixTitle = null;
      string expectedQuickFixCode = null;
      Range requestPosition = null;
      Range expectedQuickFixRange = null;
      var numberOfLines = 0;
      var positionOffset = 0;
      for (var i = 0; i < matches.Count; i++) {
        var match = matches[i];
        initialCode += source.Substring(lastPosition, match.Index - lastPosition);
        if (match.Groups["message"].Success) {
          expectedQuickFixTitle = match.Groups["message"].Value;
          expectedQuickFixCode = match.Groups["inserted"].Value;
          Position position = (numberOfLines, (match.Index + positionOffset) - lastStartOfLine);
          expectedQuickFixRange = (position, position);
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

      Assert.IsNotNull(expectedQuickFixCode, "Could not find an expected quick fix code");
      Assert.IsNotNull(expectedQuickFixTitle, "Could not find an expected quick fix title");
      Assert.IsNotNull(expectedQuickFixRange, "Could not find an expected quick fix range");

      await TestIfCodeAction(initialCode, requestPosition, expectedQuickFixTitle, expectedQuickFixCode,
        expectedQuickFixRange);
    }

    private async Task TestIfCodeAction(string source, Range requestPosition, string expectedQuickFixTitle, string expectedQuickFix,
      Range expectedQuickFixRange) {
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var verificationDiagnostics = await diagnosticReceiver.AwaitVerificationDiagnosticsAsync(CancellationToken);
      Assert.AreEqual(1, verificationDiagnostics.Length);

      var completionList = await RequestCodeActionAsync(documentItem, requestPosition);
      var found = false;
      foreach (var completion in completionList) {
        if (completion.CodeAction is { Title: var title } codeAction && title == expectedQuickFixTitle) {
          found = true;
          codeAction = await RequestResolveCodeAction(codeAction);
          var textDocumentEdit = codeAction.Edit?.DocumentChanges?.Single().TextDocumentEdit;
          Assert.IsNotNull(textDocumentEdit);
          var edit = textDocumentEdit.Edits.Single();
          Assert.AreEqual(expectedQuickFix, edit.NewText);
          Assert.AreEqual(expectedQuickFixRange, edit.Range);
        }
      }

      Assert.IsTrue(found, $"Did not find the code action '{expectedQuickFixTitle}'");
    }
  }
}
