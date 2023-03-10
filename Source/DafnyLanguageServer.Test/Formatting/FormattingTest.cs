
using System.Collections.Generic;
using System.Linq;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.Handlers;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Microsoft.Dafny.LanguageServer.Workspace;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Xunit;
using Xunit.Abstractions;

namespace Microsoft.Dafny.LanguageServer.Formatting;
public class FormattingTest : ClientBasedLanguageServerTest {
  public override async Task InitializeAsync() {
    await SetUp(o => o.ProverOptions.Add("SOLVER=noop"));
  }

  [Fact]
  public async Task TestFormatting1() {
    var source = @"
function test
       (
 a: int
        ): int {
       if   a - 1
  == 0 then
         1
         else
a + 1
    }
";
    var target = @"
function test
(
  a: int
): int {
  if   a - 1
    == 0 then
    1
  else
    a + 1
}
";
    await FormattingWorksFor(source, target);
    await FormattingWorksFor(target, target);
  }

  [Fact]
  public async Task TestFormatting2() {
    var source = @"
function Fib(i: nat): nat {
  1
} by method {
  if i <= 1 { return i; }
    var a, b, t := 0, 1, 1;
  for t := 1 to i
  invariant && b == Fib(t)
                 && a == Fib(t-1) {
         a, b := b, a + b;
      }
return b;
}
";
    var target = @"
function Fib(i: nat): nat {
  1
} by method {
  if i <= 1 { return i; }
  var a, b, t := 0, 1, 1;
  for t := 1 to i
    invariant && b == Fib(t)
              && a == Fib(t-1) {
    a, b := b, a + b;
  }
  return b;
}
";
    await FormattingWorksFor(source, target);
    await FormattingWorksFor(target, target);
  }


  [Fact]
  public async Task TestFormatting3() {
    var source = @"
predicate IsBinary(s: seq<int>) {
forall i | 0 <= i < |s| ::
|| s[i] == 0
|| s[i] == 1
}
";
    var target = @"
predicate IsBinary(s: seq<int>) {
  forall i | 0 <= i < |s| ::
    || s[i] == 0
    || s[i] == 1
}
";
    await FormattingWorksFor(source, target);
    await FormattingWorksFor(target, target);
  }

  [Fact]
  public async Task TestWhenDocIsEmpty() {
    var source = @"
";
    await FormattingWorksFor(source);
  }

  [Fact]
  public async Task TestWhenParsingFails() {
    var source = @"
function test() {
  var x := 1:
  var y = 2;
  z
}

module A {
  class B {
    method z() {
      
    }
  }
}";
    await FormattingWorksFor(source);
  }

  private async Task<List<TextEdit>> RequestFormattingAsync(TextDocumentItem documentItem) {
    var editList = await client.RequestDocumentFormatting(
      new DocumentFormattingParams {
        TextDocument = documentItem.Uri.GetFileSystemPath(),
      },
      CancellationToken
    );
    if (editList != null) {
      return editList.ToList();
    } else {
      return new List<TextEdit>();
    }
  }

  private async Task FormattingWorksFor(string source, string target = null) {
    if (target == null) {
      target = source;
    }
    var documentItem = CreateTestDocument(source);
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
    var verificationDiagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken);
    DocumentAfterParsing document = await Documents.GetLastDocumentAsync(documentItem);
    var edits = await RequestFormattingAsync(documentItem);
    edits.Reverse();
    var finalText = source;
    Assert.NotNull(document);
    var codeActionInput = new DafnyCodeActionInput(document);

    foreach (var edit in edits) {
      finalText = codeActionInput.Extract(new Range((0, 0), edit.Range.Start)) +
                  edit.NewText +
                  codeActionInput.Extract(new Range(edit.Range.End, document.TextDocumentItem.Range.End));
    }
    Assert.Equal(target, finalText);
  }

  public FormattingTest(ITestOutputHelper output) : base(output) {
  }
}
