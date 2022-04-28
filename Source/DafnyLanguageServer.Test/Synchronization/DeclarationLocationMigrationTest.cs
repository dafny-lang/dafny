using System.IO;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Linq;
using System.Threading.Tasks;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Synchronization {
  [TestClass]
  public class DeclarationLocationMigrationTest : SynchronizationTestBase {
    // The assertion Assert.IsFalse(document.SymbolTable.Resolved) is used to ensure that
    // we're working on a migrated symbol table. If that's not the case, the test case has
    // to be adapted.

    // TODO The Declaration Range currently does not incorporate keywords such as "class" and "var".
    // TODO The "BodyEndToken" used by the CreateDeclarationDictionary.CreateDeclarationDictionary()
    //      does not incorporate the closing braces.

    private bool TryFindSymbolDeclarationByName(DafnyDocument document, string symbolName, out SymbolLocation location) {
      location = document.SymbolTable.Locations
        .WithCancellation(CancellationToken)
        .Where(entry => entry.Key.Name == symbolName)
        .Select(entry => entry.Value)
        .SingleOrDefault();
      return location != null;
    }

    [TestMethod]
    public async Task MigrationLeavesLinesOfSymbolsBeforeUnchangedWhenChangingInTheMiddle() {
      var source = @"
class A {
}

class B {
}

class C {
}".TrimStart();

      var change = @"
class B {
  var x: int;

  function GetX()
}";
      var documentItem = CreateTestDocument(source);
      await Client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await ApplyChangeAndWaitCompletionAsync(
        documentItem,
        new Range((3, 0), (4, 1)),
        change
      );
      var document = await Documents.GetDocumentAsync(documentItem.Uri);
      Assert.IsNotNull(document);
      Assert.IsFalse(document.SymbolTable.Resolved);
      Assert.IsTrue(TryFindSymbolDeclarationByName(document, "A", out var location));
      Assert.AreEqual(new Range((0, 6), (0, 7)), location.Name);
      Assert.AreEqual(new Range((0, 6), (1, 0)), location.Declaration);
    }

    [TestMethod]
    public async Task MigrationLeavesLinesOfSymbolsBeforeUnchangedWhenRemovingInTheMiddle() {
      var source = @"
class A {
}

class B {
}

class C {
}".TrimStart();

      var change = "";
      var documentItem = CreateTestDocument(source);
      await Client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await ApplyChangeAndWaitCompletionAsync(
        documentItem,
        new Range((3, 0), (4, 0)),
        change
      );
      var document = await Documents.GetDocumentAsync(documentItem.Uri);
      Assert.IsNotNull(document);
      Assert.IsFalse(document.SymbolTable.Resolved);
      Assert.IsTrue(TryFindSymbolDeclarationByName(document, "A", out var location));
      Assert.AreEqual(new Range((0, 6), (0, 7)), location.Name);
      Assert.AreEqual(new Range((0, 6), (1, 0)), location.Declaration);
    }

    [TestMethod]
    public async Task MigrationMovesLinesOfSymbolsAfterWhenChangingInTheMiddle() {
      var source = @"
class A {
}

class B {
}

class C {
}".TrimStart();

      var change = @"
class B {
  var x: int;

  function GetX()
}";
      var documentItem = CreateTestDocument(source);
      await Client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await ApplyChangeAndWaitCompletionAsync(
        documentItem,
        new Range((3, 0), (4, 1)),
        change
      );
      var document = await Documents.GetDocumentAsync(documentItem.Uri);
      Assert.IsNotNull(document);
      Assert.IsFalse(document.SymbolTable.Resolved);
      Assert.IsTrue(TryFindSymbolDeclarationByName(document, "C", out var location));
      Assert.AreEqual(new Range((10, 6), (10, 7)), location.Name);
      Assert.AreEqual(new Range((10, 6), (11, 0)), location.Declaration);
    }

    [TestMethod]
    public async Task MigrationMovesLinesOfSymbolsAfterWhenRemovingInTheMiddle() {
      var source = @"
class A {
}

class B {
}

class C {
}".TrimStart();

      var change = "";
      var documentItem = CreateTestDocument(source);
      await Client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await ApplyChangeAndWaitCompletionAsync(
        documentItem,
        new Range((3, 0), (4, 0)),
        change
      );
      var document = await Documents.GetDocumentAsync(documentItem.Uri);
      Assert.IsNotNull(document);
      Assert.IsFalse(document.SymbolTable.Resolved);
      Assert.IsTrue(TryFindSymbolDeclarationByName(document, "C", out var location));
      Assert.AreEqual(new Range((5, 6), (5, 7)), location.Name);
      Assert.AreEqual(new Range((5, 6), (6, 0)), location.Declaration);
    }

    [TestMethod]
    public async Task MigrationLeavesLocationUnchangedWhenChangingAtTheEndOfTheSignature() {
      var source = @"
class A {
  var x: int;

  function GetX(): int {
    x
  }
}".TrimStart();

      var change = "string reads thi";
      var documentItem = CreateTestDocument(source);
      await Client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await ApplyChangeAndWaitCompletionAsync(
        documentItem,
        new Range((3, 19), (3, 22)),
        change
      );
      var document = await Documents.GetDocumentAsync(documentItem.Uri);
      Assert.IsNotNull(document);
      Assert.IsFalse(document.SymbolTable.Resolved);
      Assert.IsTrue(TryFindSymbolDeclarationByName(document, "GetX", out var location));
      Assert.AreEqual(new Range((3, 11), (3, 15)), location.Name);
      Assert.AreEqual(new Range((3, 11), (5, 2)), location.Declaration);
    }

    [TestMethod]
    public async Task MigrationExpandsDeclarationRangeWhenChangingTheContents() {
      var source = @"
class A {
  var x: int;
}".TrimStart();

      var change = @"var y: int;

  function GetY()";
      var documentItem = CreateTestDocument(source);
      await Client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await ApplyChangeAndWaitCompletionAsync(
        documentItem,
        new Range((1, 2), (1, 13)),
        change
      );
      var document = await Documents.GetDocumentAsync(documentItem.Uri);
      Assert.IsNotNull(document);
      Assert.IsFalse(document.SymbolTable.Resolved);
      Assert.IsTrue(TryFindSymbolDeclarationByName(document, "A", out var location));
      Assert.AreEqual(new Range((0, 6), (0, 7)), location.Name);
      Assert.AreEqual(new Range((0, 6), (4, 0)), location.Declaration);
    }

    [TestMethod]
    public async Task MigrationExpandsDeclarationRangeWhenChangingTheContentsOnTheSameLine() {
      var source = "class A { var x: int; }";
      var change = "var y: int; function GetY()";
      var documentItem = CreateTestDocument(source);
      await Client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await ApplyChangeAndWaitCompletionAsync(
        documentItem,
        new Range((0, 10), (0, 21)),
        change
      );
      var document = await Documents.GetDocumentAsync(documentItem.Uri);
      Assert.IsNotNull(document);
      Assert.IsFalse(document.SymbolTable.Resolved);
      Assert.IsTrue(TryFindSymbolDeclarationByName(document, "A", out var location));
      Assert.AreEqual(new Range((0, 6), (0, 7)), location.Name);
      Assert.AreEqual(new Range((0, 6), (0, 38)), location.Declaration);
    }

    [TestMethod]
    public async Task MigrationRemovesLocationsWithinTheChangedRange() {
      var source = @"
class A {
  var x: int;
}".TrimStart();

      var change = @"var y: int;

  function GetY()";
      var documentItem = CreateTestDocument(source);
      await Client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await ApplyChangeAndWaitCompletionAsync(
        documentItem,
        new Range((1, 2), (1, 13)),
        change
      );
      var document = await Documents.GetDocumentAsync(documentItem.Uri);
      Assert.IsNotNull(document);
      Assert.IsFalse(document.SymbolTable.Resolved);
      Assert.IsFalse(TryFindSymbolDeclarationByName(document, "x", out var _));
    }

    [TestMethod]
    public async Task MigrationMovesDeclarationWhenApplyingMultipleChangesAtOnce() {
      var source = @"
class X {
}

class B {
  var y: int;
}".TrimStart();

      var documentItem = CreateTestDocument(source);
      await Client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await ApplyChangesAndWaitCompletionAsync(
        documentItem,
        new TextDocumentContentChangeEvent {
          Range = new Range((3, 9), (3, 9)),
          Text = @"
  var x: int"
        },
        new TextDocumentContentChangeEvent {
          Range = new Range((0, 0), (1, 1)),
          Text = @"
class A {
  var a
}".TrimStart()
        }
      );
      var document = await Documents.GetDocumentAsync(documentItem.Uri);
      Assert.IsNotNull(document);
      Assert.IsFalse(document.SymbolTable.Resolved);
      Assert.IsTrue(TryFindSymbolDeclarationByName(document, "B", out var bLocation));
      Assert.AreEqual(new Range((4, 6), (4, 7)), bLocation.Name);
      Assert.AreEqual(new Range((4, 6), (7, 0)), bLocation.Declaration);
      Assert.IsTrue(TryFindSymbolDeclarationByName(document, "y", out var yLocation));
      Assert.AreEqual(new Range((6, 6), (6, 7)), yLocation.Name);
      Assert.AreEqual(new Range((6, 6), (6, 7)), yLocation.Declaration);
    }

    [TestMethod]
    public async Task PassingANullChangeRangeClearsSymbolsTable() {
      var source = "class X {}";
      var documentItem = CreateTestDocument(source);

      await Client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var document = await Documents.GetDocumentAsync(documentItem.Uri);
      Assert.IsNotNull(document);
      Assert.IsTrue(TryFindSymbolDeclarationByName(document, "X", out var _));

      // First try a change that doesn't break resolution.
      // In this case all information is recomputed and no relocation happens.
      await ApplyChangeAndWaitCompletionAsync(document.Text, null, "class Y {}");
      document = await Documents.GetDocumentAsync(document.Text.Uri);
      Assert.IsNotNull(document); // No relocation, since no resolution errors, so Y can be found
      Assert.IsFalse(TryFindSymbolDeclarationByName(document, "X", out var _));
      Assert.IsTrue(TryFindSymbolDeclarationByName(document, "Y", out var _));

      // Next try a change that breaks resolution.
      // In this case symbols are relocated.  Since the change range is `null` all symbols for "test.dfy" are lost.
      await ApplyChangeAndWaitCompletionAsync(document.Text, null, "; class Y {}");
      document = await Documents.GetDocumentAsync(document.Text.Uri);
      Assert.IsNotNull(document);
      // Relocation happens due to the syntax error; range is null so table is cleared
      Assert.IsFalse(TryFindSymbolDeclarationByName(document, "X", out var _));
      Assert.IsFalse(TryFindSymbolDeclarationByName(document, "Y", out var _));
    }


    [TestMethod]
    public async Task PassingANullChangeRangePreservesForeignSymbols() {
      var source = "include \"foreign.dfy\"\nclass X {}";
      var documentItem = CreateTestDocument(source, Path.Combine(Directory.GetCurrentDirectory(), "Lookup/TestFiles/test.dfy"));

      await Client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var document = await Documents.GetDocumentAsync(documentItem.Uri);
      Assert.IsNotNull(document);
      Assert.IsTrue(TryFindSymbolDeclarationByName(document, "A", out var _));

      // Try a change that breaks resolution.  Symbols for `foreign.dfy` are kept.
      await ApplyChangeAndWaitCompletionAsync(document.Text, null, "; include \"foreign.dfy\"\nclass Y {}");
      document = await Documents.GetDocumentAsync(document.Text.Uri);
      Assert.IsNotNull(document);
      Assert.IsTrue(TryFindSymbolDeclarationByName(document, "A", out var _));

      // Finally we drop the reference to `foreign.dfy` and confirm that `A` is not accessible any more.
      await ApplyChangeAndWaitCompletionAsync(document.Text, null, "class Y {}");
      document = await Documents.GetDocumentAsync(document.Text.Uri);
      Assert.IsNotNull(document);
      Assert.IsFalse(TryFindSymbolDeclarationByName(document, "A", out var _));
    }
  }
}