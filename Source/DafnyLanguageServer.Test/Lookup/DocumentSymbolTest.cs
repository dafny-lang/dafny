using System.Collections.Generic;
using System.IO;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Linq;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Xunit;
using Xunit.Abstractions;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Lookup {
  public class DocumentSymbolTest : ClientBasedLanguageServerTest {

    [Fact]
    public async Task BadReturnSyntax() {
      var source = @"method FindZero(a: array<int>) returns (index)  // note lack of type annotation";
      var documentItem = CreateAndOpenTestDocument(source);
      var symbols = (await RequestDocumentSymbol(documentItem)).ToList();
      CheckValidSymbols(symbols);
    }

    private void CheckValidSymbols(IEnumerable<DocumentSymbol> symbols) {
      foreach (var symbol in symbols) {
        CheckValidRange(symbol.SelectionRange);
        CheckValidRange(symbol.Range);
        CheckValidSymbols(symbol.Children);
      }
    }

    private void CheckValidRange(Range range) {
      ValidPosition(range.Start);
      ValidPosition(range.End);
    }

    private void ValidPosition(Position position) {
      Assert.True(position.Line >= 0 && position.Character >= 0);
    }

    [Fact]
    public async Task ExportImport() {
      var source = @"
module Low {
  const x := 3
}

module High {
  import Low

  export
    provides
      Low
}
".TrimStart();

      var documentItem = CreateAndOpenTestDocument(source);
      var symbols = (await RequestDocumentSymbol(documentItem)).ToList();
      Assert.Equal(2, symbols.Count);
    }

    [Fact]
    public async Task NamelessClass() {
      var source = @"class {
  function Foo(): int
  function Bar(): int
}";
      var documentItem = CreateAndOpenTestDocument(source);

      var symbols = (await RequestDocumentSymbol(documentItem)).ToList();
      Assert.True(symbols.All(s => s.Range.Start.Line >= 0));
      Assert.True(symbols.All(s => s.SelectionRange.Start.Line >= 0));
      Assert.True(symbols.All(s => !string.IsNullOrEmpty(s.Name)));
    }

    [Fact]
    public async Task NamelessModule() {
      var source = @"module {
  function Foo(): int
  function Bar(): int
}";
      var documentItem = CreateAndOpenTestDocument(source);

      var symbols = (await RequestDocumentSymbol(documentItem)).ToList();
      SymbolsAreValid(symbols);
    }

    [Fact]
    public async Task NoCrashOnJustFunction() {
      var source = "function";
      var documentItem = CreateAndOpenTestDocument(source);

      var symbols = (await RequestDocumentSymbol(documentItem)).ToList();
      SymbolsAreValid(symbols);
    }

    private static void SymbolsAreValid(List<DocumentSymbol> symbols) {
      Assert.True(symbols.All(s => s.Range.Start.Line >= 0));
      Assert.True(symbols.All(s => s.SelectionRange.Start.Line >= 0));
      Assert.True(symbols.All(s => !string.IsNullOrEmpty(s.Name)));
    }

    [Fact]
    public async Task NamelessFunction() {
      var source = "function(): int";
      var documentItem = CreateAndOpenTestDocument(source);

      var symbols = (await RequestDocumentSymbol(documentItem)).ToList();
      SymbolsAreValid(symbols);
    }

    [Fact]
    public async Task CanResolveSymbolsForMultiFileProjects() {
      var temp = GetFreshTempPath();
      await CreateOpenAndWaitForResolve("", Path.Combine(temp, DafnyProject.FileName));
      var file1 = CreateAndOpenTestDocument("method Foo() {}", Path.Combine(temp, "file1.dfy"));
      var file2 = CreateAndOpenTestDocument("method Bar() {}", Path.Combine(temp, "file2.dfy"));

      var fooSymbol = (await RequestDocumentSymbol(file1)).Single();
      Assert.Equal("Foo", fooSymbol.Name);
      var barSymbol = (await RequestDocumentSymbol(file2)).Single();
      Assert.Equal("Bar", barSymbol.Name);
    }

    [Fact]
    public async Task LoadsSymbolsInPrefixModule() {
      var source = @"
module A.B.C {

  method DoIt() returns (x: int) {
    return 2;
  }
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      client.OpenDocument(documentItem);

      var symbols = (await RequestDocumentSymbol(documentItem)).ToList();
      Assert.Single(symbols);
      var c = symbols.First();
      Assert.Equal(new Range(0, 0, 5, 1), c.Range);
      Assert.Equal(new Range(0, 11, 0, 12), c.SelectionRange);
      var cChildren = c.Children!.ToList();
      Assert.Single(cChildren);
    }

    [Fact]
    public async Task DoubleComma() {
      var source = @"
  method Foo(a: int,, b: int) returns (x: int) {
  }".TrimStart();
      var documentItem = CreateAndOpenTestDocument(source);
      var allSymbols = await RequestDocumentSymbol(documentItem);
      Assert.Single(allSymbols);
    }

    [Fact]
    public async Task LoadCorrectDocumentCreatesTopLevelSymbols() {
      var source = @"
  method DoIt() returns (x: int) {
  }

  method CallIt() returns () {
    var x := DoIt();
  }".TrimStart();
      var documentItem = CreateAndOpenTestDocument(source);
      var allSymbols = await RequestDocumentSymbol(documentItem);
      Assert.Equal(2, allSymbols.Count());
    }


    [Fact]
    public async Task LoadCorrectDocumentCreatesSymbols() {
      var source = @"
class Y {
  var z: nat;

  method DoIt() returns (x: int) {
  }

  method CallIt() returns () {
    var x := DoIt();
  }
}".TrimStart();
      var documentItem = CreateAndOpenTestDocument(source, "LoadCorrectDocumentCreatesSymbols.dfy");

      var classSymbol = (await RequestDocumentSymbol(documentItem)).Single();
      var classChildren = classSymbol.Children.ToArray();
      Assert.Equal("Y", classSymbol.Name);
      Assert.Equal(new Range((0, 6), (0, 7)), classSymbol.SelectionRange);
      Assert.Equal(new Range((0, 0), (9, 1)), classSymbol.Range);
      Assert.Equal(SymbolKind.Class, classSymbol.Kind);
      Assert.Equal(3, classChildren.Length);

      var fieldSymbol = classChildren[0];
      Assert.Equal("z", fieldSymbol.Name);
      Assert.Equal(new Range((1, 6), (1, 7)), fieldSymbol.SelectionRange);
      Assert.Equal(SymbolKind.Field, fieldSymbol.Kind);
      Assert.Empty(fieldSymbol.Children);

      var methodDoItSymbol = classChildren[1];
      var methodDoItChildren = methodDoItSymbol.Children.ToArray();
      Assert.Equal("DoIt", methodDoItSymbol.Name);
      Assert.Equal(new Range((3, 9), (3, 13)), methodDoItSymbol.SelectionRange);
      Assert.Equal(new Range((3, 2), (4, 3)), methodDoItSymbol.Range);
      Assert.Equal(SymbolKind.Method, methodDoItSymbol.Kind);
      Assert.Single(methodDoItChildren);

      var outParameterSymbol = methodDoItChildren[0];
      Assert.Equal("x", outParameterSymbol.Name);
      Assert.Equal(new Range((3, 25), (3, 26)), outParameterSymbol.SelectionRange);
      Assert.Equal(SymbolKind.Variable, outParameterSymbol.Kind);
      Assert.Empty(outParameterSymbol.Children);

      var methodCallItSymbol = classChildren[2];
      var methodCallItChildren = methodCallItSymbol.Children.ToArray();
      Assert.Equal("CallIt", methodCallItSymbol.Name);
      Assert.Equal(new Range((6, 9), (6, 15)), methodCallItSymbol.SelectionRange);
      Assert.Equal(new Range((6, 2), (8, 3)), methodCallItSymbol.Range);
      Assert.Equal(SymbolKind.Method, methodCallItSymbol.Kind);
      Assert.Single(methodCallItChildren);

      var localVariableSymbol = methodCallItChildren[0];
      Assert.Equal("x", localVariableSymbol.Name);
      Assert.Equal(new Range((7, 8), (7, 9)), localVariableSymbol.SelectionRange);
      Assert.Equal(SymbolKind.Variable, localVariableSymbol.Kind);
      Assert.Empty(localVariableSymbol.Children);
    }

    [Fact]
    public async Task CanResolveSymbolsForMethodsWithoutBody() {
      var source = "method DoIt()";
      var documentItem = CreateAndOpenTestDocument(source, "CanResolveSymbolsForMethodsWithoutBody.dfy");

      var methodSymbol = (await RequestDocumentSymbol(documentItem)).Single();
      Assert.Equal("DoIt", methodSymbol.Name);
      Assert.Equal(new Range((0, 7), (0, 11)), methodSymbol.SelectionRange);
      Assert.Equal(new Range((0, 0), (0, 13)), methodSymbol.Range);
      Assert.Equal(SymbolKind.Method, methodSymbol.Kind);
    }

    [Fact]
    public async Task CanResolveSymbolsForFunctionWithoutBody() {
      var source = "function ConstOne(): int";
      var documentItem = CreateAndOpenTestDocument(source, "CanResolveSymbolsForFunctionWithoutBody.dfy");

      var methodSymbol = (await RequestDocumentSymbol(documentItem)).Single();
      Assert.Equal("ConstOne", methodSymbol.Name);
      Assert.Equal(new Range((0, 0), (0, 24)), methodSymbol.Range);
      Assert.Equal(new Range((0, 9), (0, 17)), methodSymbol.SelectionRange);
      Assert.Equal(SymbolKind.Function, methodSymbol.Kind);
    }

    public DocumentSymbolTest(ITestOutputHelper output) : base(output) {
    }
  }
}
