using System;
using System.IO;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.Language.Symbols;
using Microsoft.Dafny.LanguageServer.Workspace;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Linq;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Microsoft.Extensions.Logging;
using Xunit;
using Xunit.Abstractions;
using Xunit.Sdk;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Synchronization {

  public class DeclarationLocationMigrationTest : SynchronizationTestBase {
    // The assertion Assert.False(document.SymbolTable.Resolved) is used to ensure that
    // we're working on a migrated symbol table. If that's not the case, the test case has
    // to be adapted.

    // TODO The Declaration Range currently does not incorporate keywords such as "class" and "var".
    // TODO The "BodyEndToken" used by the CreateDeclarationDictionary.CreateDeclarationDictionary()
    //      does not incorporate the closing braces.

    protected bool TryFindSymbolDeclarationByName(IdeState state, string symbolName, out SymbolLocation location, Uri uri = null) {
      location = state.SignatureAndCompletionTable.LocationsPerUri[uri ?? state.SignatureAndCompletionTable.LocationsPerUri.First().Key]
        .WithCancellation(CancellationToken)
        .Where(entry => entry.Key.Name == symbolName)
        .Select(entry => entry.Value)
        .SingleOrDefault();
      return location != null;
    }

    [Fact]
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
      var documentItem = CreateTestDocument(source, "MigrationLeavesLinesOfSymbolsBeforeUnchangedWhenChangingInTheMiddle.dfy");
      await Client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await ApplyChangeAndWaitCompletionAsync(
        ref documentItem,
        new Range((3, 0), (4, 1)),
        change
      );
      var document = await Projects.GetParsedDocumentNormalizeUri(documentItem.Uri);
      Assert.NotNull(document);
      Assert.True(TryFindSymbolDeclarationByName(document, "A", out var location));
      Assert.Equal(new Range((0, 6), (0, 7)), location.Name);
      Assert.Equal(new Range((0, 0), (1, 0)), location.Declaration);
    }

    [Fact]
    public async Task MigrationLeavesLinesOfSymbolsBeforeUnchangedWhenRemovingInTheMiddle() {
      var source = @"
class A {
}

class B {
}

class C {
}".TrimStart();

      var change = "";
      var documentItem = CreateTestDocument(source, "MigrationLeavesLinesOfSymbolsBeforeUnchangedWhenRemovingInTheMiddle.dfy");
      await Client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await ApplyChangeAndWaitCompletionAsync(
        ref documentItem,
        new Range((3, 0), (4, 0)),
        change
      );
      var document = await Projects.GetParsedDocumentNormalizeUri(documentItem.Uri);
      Assert.NotNull(document);
      Assert.True(TryFindSymbolDeclarationByName(document, "A", out var location));
      Assert.Equal(new Range((0, 6), (0, 7)), location.Name);
      Assert.Equal(new Range((0, 0), (1, 0)), location.Declaration);
    }


    [Fact]
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
      var documentItem = CreateTestDocument(source, "MigrationMovesLinesOfSymbolsAfterWhenChangingInTheMiddle.dfy");
      await Client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);

      await ApplyChangeAndWaitCompletionAsync(
        ref documentItem,
        new Range((3, 0), (4, 1)),
        change
      );
      var state = await Projects.GetParsedDocumentNormalizeUri(documentItem.Uri);
      Assert.NotNull(state);
      try {
        Assert.True(TryFindSymbolDeclarationByName(state, "C", out var location));
        Assert.Equal(new Range((10, 6), (10, 7)), location.Name);
        Assert.Equal(new Range((10, 0), (11, 0)), location.Declaration);
      } catch (AssertActualExpectedException) {
        await output.WriteLineAsync($"state version is {state.Version}, diagnostics: {state.GetAllDiagnostics().Stringify()}");
        var programString = new StringWriter();
        var printer = new Printer(programString, DafnyOptions.Default);
        printer.PrintProgram((Program)state.Program, true);
        await output.WriteLineAsync($"program:\n{programString}");
      }
    }

    [Fact]
    public async Task MigrationMovesLinesOfSymbolsAfterWhenRemovingInTheMiddle() {
      var source = @"
class A {
}

class B {
}

class C {
}".TrimStart();

      var change = "";
      var documentItem = CreateTestDocument(source, "MigrationMovesLinesOfSymbolsAfterWhenRemovingInTheMiddle.dfy");
      await Client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await ApplyChangeAndWaitCompletionAsync(
        ref documentItem,
        new Range((3, 0), (4, 0)),
        change
      );
      var document = await Projects.GetParsedDocumentNormalizeUri(documentItem.Uri);
      Assert.NotNull(document);
      Assert.True(TryFindSymbolDeclarationByName(document, "C", out var location));
      Assert.Equal(new Range((5, 6), (5, 7)), location.Name);
      Assert.Equal(new Range((5, 0), (6, 0)), location.Declaration);
    }

    [Fact]
    public async Task MigrationLeavesLocationUnchangedWhenChangingAtTheEndOfTheSignature() {
      var source = @"
class A {
  var x: int;

  function GetX(): int {
    x
  }
}".TrimStart();

      var change = "string reads thi";
      var documentItem = CreateTestDocument(source, "MigrationLeavesLocationUnchangedWhenChangingAtTheEndOfTheSignature.dfy");
      await Client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);

      await ApplyChangeAndWaitCompletionAsync(
        ref documentItem,
        new Range((3, 19), (3, 22)),
        change
      );
      var state = await Projects.GetResolvedDocumentAsyncNormalizeUri(documentItem.Uri);
      Assert.NotNull(state);
      Assert.True(TryFindSymbolDeclarationByName(state, "GetX", out var location));
      Assert.Equal(new Range((3, 11), (3, 15)), location.Name);
      Assert.Equal(new Range((3, 2), (5, 3)), location.Declaration);
    }

    [Fact]
    public async Task MigrationExpandsDeclarationRangeWhenChangingTheContents() {
      var source = @"
class A {
  var x: int;
}".TrimStart();

      var change = @"var y: int;

  function GetY()";
      var documentItem = CreateTestDocument(source, "MigrationExpandsDeclarationRangeWhenChangingTheContents.dfy");
      await Client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await ApplyChangeAndWaitCompletionAsync(
        ref documentItem,
        new Range((1, 2), (1, 13)),
        change
      );
      var document = await Projects.GetParsedDocumentNormalizeUri(documentItem.Uri);
      Assert.NotNull(document);
      Assert.True(TryFindSymbolDeclarationByName(document, "A", out var location));
      Assert.Equal(new Range((0, 6), (0, 7)), location.Name);
      Assert.Equal(new Range((0, 0), (4, 0)), location.Declaration);
    }

    [Fact]
    public async Task MigrationExpandsDeclarationRangeWhenChangingTheContentsOnTheSameLine() {
      var source = "class A { var x: int; }";
      var change = "var y: int; function GetY()";
      var documentItem = CreateTestDocument(source, "MigrationExpandsDeclarationRangeWhenChangingTheContentsOnTheSameLine.dfy");
      await Client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await ApplyChangeAndWaitCompletionAsync(
        ref documentItem,
        new Range((0, 10), (0, 21)),
        change
      );
      var document = await Projects.GetParsedDocumentNormalizeUri(documentItem.Uri);
      Assert.NotNull(document);
      Assert.True(TryFindSymbolDeclarationByName(document, "A", out var location));
      Assert.Equal(new Range((0, 6), (0, 7)), location.Name);
      Assert.Equal(new Range((0, 0), (0, 38)), location.Declaration);
    }

    [Fact]
    public async Task MigrationRemovesLocationsWithinTheChangedRange() {
      var source = @"
class A {
  var x: int;
}".TrimStart();

      var change = @"var y: int;

  function GetY()";
      var documentItem = CreateTestDocument(source, "MigrationRemovesLocationsWithinTheChangedRange.dfy");
      await Client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await ApplyChangeAndWaitCompletionAsync(
        ref documentItem,
        new Range((1, 2), (1, 13)),
        change
      );
      var document = await Projects.GetParsedDocumentNormalizeUri(documentItem.Uri);
      Assert.NotNull(document);
      Assert.False(TryFindSymbolDeclarationByName(document, "x", out var _));
    }

    [Fact]
    public async Task MigrationMovesDeclarationWhenApplyingMultipleChangesAtOnce() {
      var source = @"
class X {
}

class B {
  var y: int;
}".TrimStart();

      var documentItem = CreateTestDocument(source, "MigrationMovesDeclarationWhenApplyingMultipleChangesAtOnce.dfy");
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
      var document = await Projects.GetParsedDocumentNormalizeUri(documentItem.Uri);
      Assert.NotNull(document);
      Assert.True(TryFindSymbolDeclarationByName(document, "B", out var bLocation));
      Assert.Equal(new Range((4, 6), (4, 7)), bLocation.Name);
      Assert.Equal(new Range((4, 0), (7, 0)), bLocation.Declaration);
      Assert.True(TryFindSymbolDeclarationByName(document, "y", out var yLocation));
      Assert.Equal(new Range((6, 6), (6, 7)), yLocation.Name);
      Assert.Equal(new Range((6, 2), (6, 12)), yLocation.Declaration);
    }

    [Fact]
    public async Task PassingANullChangeRangeClearsSymbolsTable() {
      var source = "class X {}";
      var documentItem = CreateTestDocument(source, "PassingANullChangeRangeClearsSymbolsTable.dfy");

      await Client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var state = await Projects.GetResolvedDocumentAsyncNormalizeUri(documentItem.Uri);
      Assert.NotNull(state);
      Assert.True(TryFindSymbolDeclarationByName(state, "X", out var _));

      // First try a change that doesn't break resolution.
      // In this case all information is recomputed and no relocation happens.
      await ApplyChangeAndWaitCompletionAsync(ref documentItem, null, "class Y {}");
      state = await Projects.GetResolvedDocumentAsyncNormalizeUri(documentItem);
      Assert.NotNull(state); // No relocation, since no resolution errors, so Y can be found
      Assert.False(TryFindSymbolDeclarationByName(state, "X", out var _));
      Assert.True(TryFindSymbolDeclarationByName(state, "Y", out var _));

      // Next try a change that breaks resolution.
      // In this case symbols are relocated.  Since the change range is `null` all symbols for "test.dfy" are lost.
      await ApplyChangeAndWaitCompletionAsync(ref documentItem, null, "; class Y {}");
      state = await Projects.GetParsedDocumentNormalizeUri(documentItem);
      Assert.NotNull(state);
      // Relocation happens due to the syntax error; range is null so table is cleared
      Assert.False(TryFindSymbolDeclarationByName(state, "X", out var _));
      Assert.False(TryFindSymbolDeclarationByName(state, "Y", out var _));
    }


    [Fact]
    public async Task PassingANullChangeRangePreservesForeignSymbols() {
      var directory = Path.Combine(Directory.GetCurrentDirectory(), "Lookup/TestFiles");
      var source = "include \"foreign.dfy\"\nclass X {}";
      var documentItem = CreateTestDocument(source, Path.Combine(directory, "test.dfy"));
      var includePath = Path.Combine(directory, "foreign.dfy");

      await Client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var document = await Projects.GetResolvedDocumentAsyncNormalizeUri(documentItem.Uri);
      Assert.NotNull(document);
      var uri = documentItem.Uri.ToUri();
      Assert.True(TryFindSymbolDeclarationByName(document, "A", out var _, new Uri(includePath)));

      // Try a change that breaks resolution.  Symbols for `foreign.dfy` are kept.
      await ApplyChangeAndWaitCompletionAsync(ref documentItem, null, "; include \"foreign.dfy\"\nclass Y {}");
      document = await Projects.GetParsedDocumentNormalizeUri(documentItem);
      Assert.NotNull(document);
      Assert.True(TryFindSymbolDeclarationByName(document, "A", out var _, new Uri(includePath)));

      // Finally we drop the reference to `foreign.dfy` and confirm that `A` is not accessible any more.
      await ApplyChangeAndWaitCompletionAsync(ref documentItem, null, "class Y {}");
      document = await Projects.GetResolvedDocumentAsyncNormalizeUri(documentItem);
      Assert.NotNull(document);
      Assert.False(TryFindSymbolDeclarationByName(document, "A", out var _, uri));
    }

    public DeclarationLocationMigrationTest(ITestOutputHelper output) : this(output, LogLevel.Information) {
    }

    protected DeclarationLocationMigrationTest(ITestOutputHelper output, LogLevel logLevel) : base(output, logLevel) {
    }
  }
}
