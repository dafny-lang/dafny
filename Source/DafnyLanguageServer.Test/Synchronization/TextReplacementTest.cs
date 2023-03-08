using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Threading.Tasks;
using Xunit.Abstractions;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Synchronization {
  [TestClass]
  public class TextReplacementTest : SynchronizationTestBase {
    [TestMethod]
    public async Task ReplaceSingleLineTextAtStart() {
      var source = @"
function GetConstant(): int {
  1
}".TrimStart();
      var change = "function GetIt():int";
      var documentItem = CreateTestDocument(source);
      await Client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await ApplyChangeAndWaitCompletionAsync(
        documentItem,
        new Range((0, 0), (0, 27)),
        change
      );
      var document = await Documents.GetResolvedDocumentAsync(documentItem.Uri);
      Assert.IsNotNull(document);
      var expected = @"
function GetIt():int {
  1
}".TrimStart();
      Assert.AreEqual(expected, document.TextDocumentItem.Text);
    }

    [TestMethod]
    public async Task ReplaceMultiLineTextAtStart() {
      var source = @"
function GetConstant(): int {
  1
}".TrimStart();
      var change = @"function Get21(): int
{
  2";
      var documentItem = CreateTestDocument(source);
      await Client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await ApplyChangeAndWaitCompletionAsync(
        documentItem,
        new Range((0, 0), (1, 2)),
        change
      );
      var document = await Documents.GetResolvedDocumentAsync(documentItem.Uri);
      Assert.IsNotNull(document);
      var expected = @"
function Get21(): int
{
  21
}".TrimStart();
      Assert.AreEqual(expected, document.TextDocumentItem.Text);
    }

    [TestMethod]
    public async Task ReplaceSingleLineTextAtEnd() {
      var source = @"
function GetConstant(): int {
  1
}".TrimStart();
      var change = "/* test */ }";
      var documentItem = CreateTestDocument(source);
      await Client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await ApplyChangeAndWaitCompletionAsync(
        documentItem,
        new Range((2, 0), (2, 1)),
        change
      );
      var document = await Documents.GetResolvedDocumentAsync(documentItem.Uri);
      Assert.IsNotNull(document);
      var expected = @"
function GetConstant(): int {
  1
/* test */ }".TrimStart();
      Assert.AreEqual(expected, document.TextDocumentItem.Text);
    }

    [TestMethod]
    public async Task ReplaceMultiLineTextAtEnd() {
      var source = @"
function GetConstant(): int {
  1
}".TrimStart();
      var change = @"
23
/* test */ }".TrimStart();
      var documentItem = CreateTestDocument(source);
      await Client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await ApplyChangeAndWaitCompletionAsync(
        documentItem,
        new Range((1, 2), (2, 1)),
        change
      );
      var document = await Documents.GetResolvedDocumentAsync(documentItem.Uri);
      Assert.IsNotNull(document);
      var expected = @"
function GetConstant(): int {
  23
/* test */ }".TrimStart();
      Assert.AreEqual(expected, document.TextDocumentItem.Text);
    }

    [TestMethod]
    public async Task ReplaceMultiLineTextInTheMiddle() {
      var source = @"
class Test {
    var x: int;
    var y: int;

    function GetX(): int
        reads this
    {
        this.x
    }

    function GetSum(): int
        reads this
    {
        this.x + this.y
    }

    function GetY(): int
        reads this
    {
        this.y
    }
}".TrimStart();
      var change = @"
method GetXY() returns (x: int, y: int)
    {
        x := this.x;
        y := ".TrimStart();
      var documentItem = CreateTestDocument(source);
      await Client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await ApplyChangeAndWaitCompletionAsync(
        documentItem,
        new Range((10, 4), (13, 17)),
        change
      );
      var document = await Documents.GetResolvedDocumentAsync(documentItem.Uri);
      Assert.IsNotNull(document);
      var expected = @"
class Test {
    var x: int;
    var y: int;

    function GetX(): int
        reads this
    {
        this.x
    }

    method GetXY() returns (x: int, y: int)
    {
        x := this.x;
        y := this.y
    }

    function GetY(): int
        reads this
    {
        this.y
    }
}".TrimStart();
      Assert.AreEqual(expected, document.TextDocumentItem.Text);
    }

    [TestMethod]
    public async Task ReplaceSingleLineTextInTheMiddleOfALine() {
      var source = @"
function GetConstant(): int {
  1
}".TrimStart();
      var change = "Another";
      var documentItem = CreateTestDocument(source);
      await Client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await ApplyChangeAndWaitCompletionAsync(
        documentItem,
        new Range((0, 12), (0, 20)),
        change
      );
      var document = await Documents.GetResolvedDocumentAsync(documentItem.Uri);
      Assert.IsNotNull(document);
      var expected = @"
function GetAnother(): int {
  1
}".TrimStart();
      Assert.AreEqual(expected, document.TextDocumentItem.Text);
    }

    [TestMethod]
    public async Task ReplaceMultiLineTextInTheMiddleOfALine() {
      var source = @"
function GetConstant(): int {
  1
}".TrimStart();
      var change = @"It(): string {
  ""test""
}

function Some";
      var documentItem = CreateTestDocument(source);
      await Client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await ApplyChangeAndWaitCompletionAsync(
        documentItem,
        new Range((0, 9), (0, 20)),
        change
      );
      var document = await Documents.GetResolvedDocumentAsync(documentItem.Uri);
      Assert.IsNotNull(document);
      var expected = @"
function It(): string {
  ""test""
}

function Some(): int {
  1
}".TrimStart();
      Assert.AreEqual(expected, document.TextDocumentItem.Text);
    }

    [TestMethod]
    public async Task RemoveCompleteDocumentContent() {
      var source = @"
function GetConstant(): int {
  1
}".TrimStart();
      var change = "";
      var documentItem = CreateTestDocument(source);
      await Client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await ApplyChangeAndWaitCompletionAsync(
        documentItem,
        new Range((0, 0), (2, 1)),
        change
      );
      var document = await Documents.GetResolvedDocumentAsync(documentItem.Uri);
      Assert.IsNotNull(document);
      var expected = "";
      Assert.AreEqual(expected, document.TextDocumentItem.Text);
    }

    [TestMethod]
    public async Task ReplaceCompleteDocumentContent() {
      var source = "ghost function GetConstant(): int { 1 }";
      var change = "function ReturnSame(x: int): int { x }";
      var documentItem = CreateTestDocument(source);
      await Client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await ApplyChangeAndWaitCompletionAsync(documentItem, null, change);
      var document = await Documents.GetResolvedDocumentAsync(documentItem.Uri);
      Assert.IsNotNull(document);
      Assert.AreEqual(change, document.TextDocumentItem.Text);
    }

    public TextReplacementTest(ITestOutputHelper output) : base(output)
    {
    }
  }
}
