using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Threading.Tasks;
using Xunit.Abstractions;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Synchronization {
  [TestClass]
  public class TextInsertionTest : SynchronizationTestBase {
    [TestMethod]
    public async Task InsertTextAtStart() {
      var source = @"
function GetConstant(): int {
  1
}".TrimStart();
      var change = @"
function GetConstant2(): int {
  2
}

".TrimStart();
      var documentItem = CreateTestDocument(source);
      await Client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await ApplyChangeAndWaitCompletionAsync(
        documentItem,
        new Range((0, 0), (0, 0)),
        change
      );
      var document = await Documents.GetResolvedDocumentAsync(documentItem.Uri);
      Assert.IsNotNull(document);
      var expected = @"
function GetConstant2(): int {
  2
}

function GetConstant(): int {
  1
}".TrimStart();
      Assert.AreEqual(expected, document.TextDocumentItem.Text);
    }

    [TestMethod]
    public async Task InsertTextAtEnd() {
      var source = @"
function GetConstant(): int {
  1
}

".TrimStart();
      var change = @"
function GetConstant2(): int {
  2
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await Client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await ApplyChangeAndWaitCompletionAsync(
        documentItem,
        new Range((4, 0), (4, 0)),
        change
      );
      var document = await Documents.GetResolvedDocumentAsync(documentItem.Uri);
      Assert.IsNotNull(document);
      var expected = @"
function GetConstant(): int {
  1
}

function GetConstant2(): int {
  2
}".TrimStart();
      Assert.AreEqual(expected, document.TextDocumentItem.Text);
    }

    [TestMethod]
    public async Task InsertTextInTheMiddle() {
      var source = @"
function GetConstant(): int {
  1
}

function GetConstant3(): int {
  3
}".TrimStart();
      var change = @"
function GetConstant2(): int {
  2
}

".TrimStart();
      var documentItem = CreateTestDocument(source);
      await Client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await ApplyChangeAndWaitCompletionAsync(
        documentItem,
        new Range((4, 0), (4, 0)),
        change
      );
      var document = await Documents.GetResolvedDocumentAsync(documentItem.Uri);
      Assert.IsNotNull(document);
      var expected = @"
function GetConstant(): int {
  1
}

function GetConstant2(): int {
  2
}

function GetConstant3(): int {
  3
}".TrimStart();
      Assert.AreEqual(expected, document.TextDocumentItem.Text);
    }

    [TestMethod]
    public async Task InsertSingleLineTextInTheMiddleOfALine() {
      var source = @"
function GetConstant(): int {
  1
}".TrimStart();
      var change = "Another";
      var documentItem = CreateTestDocument(source);
      await Client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await ApplyChangeAndWaitCompletionAsync(
        documentItem,
        new Range((0, 12), (0, 12)),
        change
      );
      var document = await Documents.GetResolvedDocumentAsync(documentItem.Uri);
      Assert.IsNotNull(document);
      var expected = @"
function GetAnotherConstant(): int {
  1
}".TrimStart();
      Assert.AreEqual(expected, document.TextDocumentItem.Text);
    }

    [TestMethod]
    public async Task InsertMultiLineTextInTheMiddleOfALine() {
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
        new Range((0, 12), (0, 12)),
        change
      );
      var document = await Documents.GetResolvedDocumentAsync(documentItem.Uri);
      Assert.IsNotNull(document);
      var expected = @"
function GetIt(): string {
  ""test""
}

function SomeConstant(): int {
  1
}".TrimStart();
      Assert.AreEqual(expected, document.TextDocumentItem.Text);
    }

    [TestMethod]
    public async Task InsertMultipleInSingleChange() {
      // Note: line breaks are explicitly defined to avoid compatibility issues of \r and \r\n between
      // the change and the verification.
      var source = "function GetConstant(): int { 1 }";
      var documentItem = CreateTestDocument(source);
      await Client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await ApplyChangesAndWaitCompletionAsync(
        documentItem,
        new TextDocumentContentChangeEvent {
          Range = new Range((0, 0), (0, 0)),
          Text = @"class Test {
"
        },
        new TextDocumentContentChangeEvent {
          Range = new Range((1, 0), (1, 0)),
          Text = "  "
        },
        new TextDocumentContentChangeEvent {
          Range = new Range((1, 35), (1, 35)),
          Text = @"
"
        },
        new TextDocumentContentChangeEvent {
          Range = new Range((2, 0), (2, 0)),
          Text = "}"
        }
      );
      var document = await Documents.GetResolvedDocumentAsync(documentItem.Uri);
      Assert.IsNotNull(document);
      var expected = @"
class Test {
  function GetConstant(): int { 1 }
}".TrimStart();
      Assert.AreEqual(expected, document.TextDocumentItem.Text);
    }

    public TextInsertionTest(ITestOutputHelper output) : base(output)
    {
    }
  }
}
