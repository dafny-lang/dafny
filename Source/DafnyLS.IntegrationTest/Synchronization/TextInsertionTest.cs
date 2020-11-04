using DafnyLS.IntegrationTest.Extensions;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Threading.Tasks;

namespace DafnyLS.IntegrationTest.Synchronization {
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
      Client.OpenDocument(documentItem);
      await ApplyChangeAndWaitCompletionAsync(
        documentItem,
        new Range((0, 0), (0, 0)),
        change
      );
      Assert.IsTrue(Documents.TryGetDocument(documentItem.Uri, out var document));
      var expected = @"
function GetConstant2(): int {
  2
}

function GetConstant(): int {
  1
}".TrimStart();
      Assert.AreEqual(expected, document.Text.Text);
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
      Client.OpenDocument(documentItem);
      await ApplyChangeAndWaitCompletionAsync(
        documentItem,
        new Range((4, 0), (4, 0)),
        change
      );
      Assert.IsTrue(Documents.TryGetDocument(documentItem.Uri, out var document));
      var expected = @"
function GetConstant(): int {
  1
}

function GetConstant2(): int {
  2
}".TrimStart();
      Assert.AreEqual(expected, document.Text.Text);
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
      Client.OpenDocument(documentItem);
      await ApplyChangeAndWaitCompletionAsync(
        documentItem,
        new Range((4, 0), (4, 0)),
        change
      );
      Assert.IsTrue(Documents.TryGetDocument(documentItem.Uri, out var document));
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
      Assert.AreEqual(expected, document.Text.Text);
    }

    [TestMethod]
    public async Task InsertSingleLineTextInTheMiddleOfALine() {
      var source = @"
function GetConstant(): int {
  1
}".TrimStart();
      var change = "Another";
      var documentItem = CreateTestDocument(source);
      Client.OpenDocument(documentItem);
      await ApplyChangeAndWaitCompletionAsync(
        documentItem,
        new Range((0, 12), (0, 12)),
        change
      );
      Assert.IsTrue(Documents.TryGetDocument(documentItem.Uri, out var document));
      var expected = @"
function GetAnotherConstant(): int {
  1
}".TrimStart();
      Assert.AreEqual(expected, document.Text.Text);
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
      Client.OpenDocument(documentItem);
      await ApplyChangeAndWaitCompletionAsync(
        documentItem,
        new Range((0, 12), (0, 12)),
        change
      );
      Assert.IsTrue(Documents.TryGetDocument(documentItem.Uri, out var document));
      var expected = @"
function GetIt(): string {
  ""test""
}

function SomeConstant(): int {
  1
}".TrimStart();
      Assert.AreEqual(expected, document.Text.Text);
    }
  }
}
