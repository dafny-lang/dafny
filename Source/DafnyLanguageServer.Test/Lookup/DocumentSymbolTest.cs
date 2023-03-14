using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.Linq;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Xunit;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Lookup {
  public class DocumentSymbolTest : ClientBasedLanguageServerTest {

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
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);

      var classSymbol = (await RequestDocumentSymbol(documentItem)).Single();
      var classChildren = classSymbol.Children.ToArray();
      Assert.Equal("Y", classSymbol.Name);
      Assert.Equal(new Range((0, 6), (0, 7)), classSymbol.SelectionRange);
      Assert.Equal(new Range((0, 0), (9, 0)), classSymbol.Range);
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
      Assert.Equal(new Range((3, 2), (4, 2)), methodDoItSymbol.Range);
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
      Assert.Equal(new Range((6, 2), (8, 2)), methodCallItSymbol.Range);
      Assert.Equal(SymbolKind.Method, methodCallItSymbol.Kind);
      Assert.Single(methodCallItChildren);

      var localVariableSymbol = methodCallItChildren[0];
      Assert.Equal("x", localVariableSymbol.Name);
      Assert.Equal(new Range((7, 8), (7, 9)), localVariableSymbol.SelectionRange);
      Assert.Equal(SymbolKind.Variable, localVariableSymbol.Kind);
      Assert.Empty(localVariableSymbol.Children);
    }

    [Fact]
    public async Task LoadCorrectDocumentAndChangeToInvalidCreatesPartialSymbols() {
      var source = @"
class Y {
  var z: nat;

  method DoIt() returns (x: int) {
  }

  method CallIt() returns () {
    var x := DoIt();
  }
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      client.DidChangeTextDocument(new DidChangeTextDocumentParams {
        TextDocument = new OptionalVersionedTextDocumentIdentifier {
          Uri = documentItem.Uri,
          Version = documentItem.Version + 1
        },
        ContentChanges = new[] {
          new TextDocumentContentChangeEvent {
            Range = new Range((3, 11), (4, 3)),
            Text = ""
          }
        }
      });

      var classSymbol = (await RequestDocumentSymbol(documentItem)).Single();
      var classChildren = classSymbol.Children.ToArray();
      Assert.Equal("Y", classSymbol.Name);
      Assert.Equal(new Range((0, 0), (8, 0)), classSymbol.Range);
      Assert.Equal(new Range((0, 6), (0, 7)), classSymbol.SelectionRange);
      Assert.Equal(SymbolKind.Class, classSymbol.Kind);
      Assert.Equal(2, classChildren.Length);

      var fieldSymbol = classChildren[0];
      Assert.Equal("z", fieldSymbol.Name);
      Assert.Equal(new Range((1, 6), (1, 7)), fieldSymbol.SelectionRange);
      Assert.Equal(SymbolKind.Field, fieldSymbol.Kind);
      Assert.Empty(fieldSymbol.Children);

      var methodCallItSymbol = classChildren[1];
      var methodCallItChildren = methodCallItSymbol.Children.ToArray();
      Assert.Equal("CallIt", methodCallItSymbol.Name);
      Assert.Equal(new Range((5, 9), (5, 15)), methodCallItSymbol.SelectionRange);
      Assert.Equal(new Range((5, 2), (7, 2)), methodCallItSymbol.Range);
      Assert.Equal(SymbolKind.Method, methodCallItSymbol.Kind);
      Assert.Single(methodCallItChildren);

      var localVariableSymbol = methodCallItChildren[0];
      Assert.Equal("x", localVariableSymbol.Name);
      Assert.Equal(new Range((6, 8), (6, 9)), localVariableSymbol.SelectionRange);
      Assert.Equal(SymbolKind.Variable, localVariableSymbol.Kind);
      Assert.Empty(localVariableSymbol.Children);
    }

    [Fact]
    public async Task CanResolveSymbolsForMethodsWithoutBody() {
      var source = "method DoIt()";
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);

      var methodSymbol = (await RequestDocumentSymbol(documentItem)).Single();
      Assert.Equal("DoIt", methodSymbol.Name);
      Assert.Equal(new Range((0, 7), (0, 11)), methodSymbol.SelectionRange);
      Assert.Equal(new Range((0, 0), (0, 12)), methodSymbol.Range);
      Assert.Equal(SymbolKind.Method, methodSymbol.Kind);
    }

    [Fact]
    public async Task CanResolveSymbolsForFunctionWithoutBody() {
      var source = "function ConstOne(): int";
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);

      var methodSymbol = (await RequestDocumentSymbol(documentItem)).Single();
      Assert.Equal("ConstOne", methodSymbol.Name);
      Assert.Equal(new Range((0, 0), (0, 21)), methodSymbol.Range);
      Assert.Equal(new Range((0, 9), (0, 17)), methodSymbol.SelectionRange);
      Assert.Equal(SymbolKind.Function, methodSymbol.Kind);
    }
  }
}
