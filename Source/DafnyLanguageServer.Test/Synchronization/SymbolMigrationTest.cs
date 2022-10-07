using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Linq;
using System.Threading.Tasks;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Synchronization {
  [TestClass]
  public class SymbolMigrationTest : SynchronizationTestBase {
    [TestMethod]
    public async Task ChangeToSemanticallyCorrectDocumentUsesDafnyResolver() {
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
      Assert.IsTrue(document.SignatureAndCompletionTable.Resolved);
      Assert.AreEqual(2, document.SignatureAndCompletionTable.Locations.Keys.OfType<FunctionSymbol>().Count());
    }

    [TestMethod]
    public async Task ChangeToSemanticallyIncorrectDocumentUsesMigration() {
      var source = @"
function GetConstant(): int {
  1
}".TrimStart();
      var change = @"
function GetConstant2(): int {
  ""test""
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
    }

    [TestMethod]
    public async Task ChangeToSyntacticallyIncorrectDocumentUsesMigration() {
      var source = @"
function GetConstant(): int {
  1
}

".TrimStart();
      var change = "function GetConstant2(): int {";
      var documentItem = CreateTestDocument(source);
      await Client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await ApplyChangeAndWaitCompletionAsync(
        documentItem,
        new Range((4, 0), (4, 0)),
        change
      );
      var document = await Documents.GetResolvedDocumentAsync(documentItem.Uri);
      Assert.IsNotNull(document);
    }

    [TestMethod]
    public async Task ChangeToDocumentWithVerificationErrorsUsesDafnyResolver() {
      var source = @"
method GetIt(x: int) returns (y: int) {
  return x;
}".TrimStart();
      var change = @"
  if x == 0 {
    y := 0;
  } else {
    y := GetIt(x - 1);
  }";
      var documentItem = CreateTestDocument(source);
      await Client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await ApplyChangeAndWaitCompletionAsync(
        documentItem,
        new Range((1, 0), (1, 11)),
        change
      );
      var document = await Documents.GetResolvedDocumentAsync(documentItem.Uri);
      Assert.IsNotNull(document);
      Assert.IsTrue(document.SignatureAndCompletionTable.Resolved);
      Assert.AreEqual(1, document.SignatureAndCompletionTable.Locations.Keys.OfType<MethodSymbol>().Count());
    }
  }
}
