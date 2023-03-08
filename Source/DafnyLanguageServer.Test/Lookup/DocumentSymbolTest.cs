using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using OmniSharp.Extensions.LanguageServer.Protocol.Client;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using OmniSharp.Extensions.LanguageServer.Protocol.Progress;
using System.Collections.Generic;
using System.Linq;
using System.Reactive.Linq;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Xunit.Abstractions;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Lookup {
  [TestClass]
  public class DocumentSymbolTest : ClientBasedLanguageServerTest {

    [TestMethod]
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
      Assert.AreEqual("Y", classSymbol.Name);
      Assert.AreEqual(new Range((0, 6), (0, 7)), classSymbol.SelectionRange);
      Assert.AreEqual(new Range((0, 0), (9, 0)), classSymbol.Range);
      Assert.AreEqual(SymbolKind.Class, classSymbol.Kind);
      Assert.AreEqual(3, classChildren.Length);

      var fieldSymbol = classChildren[0];
      Assert.AreEqual("z", fieldSymbol.Name);
      Assert.AreEqual(new Range((1, 6), (1, 7)), fieldSymbol.SelectionRange);
      Assert.AreEqual(SymbolKind.Field, fieldSymbol.Kind);
      Assert.AreEqual(0, fieldSymbol.Children.Count());

      var methodDoItSymbol = classChildren[1];
      var methodDoItChildren = methodDoItSymbol.Children.ToArray();
      Assert.AreEqual("DoIt", methodDoItSymbol.Name);
      Assert.AreEqual(new Range((3, 9), (3, 13)), methodDoItSymbol.SelectionRange);
      Assert.AreEqual(new Range((3, 2), (4, 2)), methodDoItSymbol.Range);
      Assert.AreEqual(SymbolKind.Method, methodDoItSymbol.Kind);
      Assert.AreEqual(1, methodDoItChildren.Length);

      var outParameterSymbol = methodDoItChildren[0];
      Assert.AreEqual("x", outParameterSymbol.Name);
      Assert.AreEqual(new Range((3, 25), (3, 26)), outParameterSymbol.SelectionRange);
      Assert.AreEqual(SymbolKind.Variable, outParameterSymbol.Kind);
      Assert.AreEqual(0, outParameterSymbol.Children.Count());

      var methodCallItSymbol = classChildren[2];
      var methodCallItChildren = methodCallItSymbol.Children.ToArray();
      Assert.AreEqual("CallIt", methodCallItSymbol.Name);
      Assert.AreEqual(new Range((6, 9), (6, 15)), methodCallItSymbol.SelectionRange);
      Assert.AreEqual(new Range((6, 2), (8, 2)), methodCallItSymbol.Range);
      Assert.AreEqual(SymbolKind.Method, methodCallItSymbol.Kind);
      Assert.AreEqual(1, methodCallItChildren.Length);

      var localVariableSymbol = methodCallItChildren[0];
      Assert.AreEqual("x", localVariableSymbol.Name);
      Assert.AreEqual(new Range((7, 8), (7, 9)), localVariableSymbol.SelectionRange);
      Assert.AreEqual(SymbolKind.Variable, localVariableSymbol.Kind);
      Assert.AreEqual(0, localVariableSymbol.Children.Count());
    }

    [TestMethod]
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
      Assert.AreEqual("Y", classSymbol.Name);
      Assert.AreEqual(new Range((0, 0), (8, 0)), classSymbol.Range);
      Assert.AreEqual(new Range((0, 6), (0, 7)), classSymbol.SelectionRange);
      Assert.AreEqual(SymbolKind.Class, classSymbol.Kind);
      Assert.AreEqual(2, classChildren.Length);

      var fieldSymbol = classChildren[0];
      Assert.AreEqual("z", fieldSymbol.Name);
      Assert.AreEqual(new Range((1, 6), (1, 7)), fieldSymbol.SelectionRange);
      Assert.AreEqual(SymbolKind.Field, fieldSymbol.Kind);
      Assert.AreEqual(0, fieldSymbol.Children.Count());

      var methodCallItSymbol = classChildren[1];
      var methodCallItChildren = methodCallItSymbol.Children.ToArray();
      Assert.AreEqual("CallIt", methodCallItSymbol.Name);
      Assert.AreEqual(new Range((5, 9), (5, 15)), methodCallItSymbol.SelectionRange);
      Assert.AreEqual(new Range((5, 2), (7, 2)), methodCallItSymbol.Range);
      Assert.AreEqual(SymbolKind.Method, methodCallItSymbol.Kind);
      Assert.AreEqual(1, methodCallItChildren.Length);

      var localVariableSymbol = methodCallItChildren[0];
      Assert.AreEqual("x", localVariableSymbol.Name);
      Assert.AreEqual(new Range((6, 8), (6, 9)), localVariableSymbol.SelectionRange);
      Assert.AreEqual(SymbolKind.Variable, localVariableSymbol.Kind);
      Assert.AreEqual(0, localVariableSymbol.Children.Count());
    }

    [TestMethod]
    public async Task CanResolveSymbolsForMethodsWithoutBody() {
      var source = "method DoIt()";
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);

      var methodSymbol = (await RequestDocumentSymbol(documentItem)).Single();
      Assert.AreEqual("DoIt", methodSymbol.Name);
      Assert.AreEqual(new Range((0, 7), (0, 11)), methodSymbol.SelectionRange);
      Assert.AreEqual(new Range((0, 0), (0, 12)), methodSymbol.Range);
      Assert.AreEqual(SymbolKind.Method, methodSymbol.Kind);
    }

    [TestMethod]
    public async Task CanResolveSymbolsForFunctionWithoutBody() {
      var source = "function ConstOne(): int";
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);

      var methodSymbol = (await RequestDocumentSymbol(documentItem)).Single();
      Assert.AreEqual("ConstOne", methodSymbol.Name);
      Assert.AreEqual(new Range((0, 0), (0, 21)), methodSymbol.Range);
      Assert.AreEqual(new Range((0, 9), (0, 17)), methodSymbol.SelectionRange);
      Assert.AreEqual(SymbolKind.Function, methodSymbol.Kind);
    }

    public DocumentSymbolTest(ITestOutputHelper output) : base(output)
    {
    }
  }
}
