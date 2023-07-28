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
    public async Task CanResolveSymbolsForMultiFileProjects() {
      var temp = Path.GetTempPath();
      await CreateAndOpenTestDocument("", Path.Combine(temp, DafnyProject.FileName));
      var file1 = await CreateAndOpenTestDocument("method Foo() {}", Path.Combine(temp, "file1.dfy"));
      var file2 = await CreateAndOpenTestDocument("method Bar() {}", Path.Combine(temp, "file2.dfy"));

      var fooSymbol = (await RequestDocumentSymbol(file1)).Single();
      Assert.Equal("Foo", fooSymbol.Name);
      var barSymbol = (await RequestDocumentSymbol(file2)).Single();
      Assert.Equal("Bar", barSymbol.Name);
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
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);

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
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);

      var methodSymbol = (await RequestDocumentSymbol(documentItem)).Single();
      Assert.Equal("DoIt", methodSymbol.Name);
      Assert.Equal(new Range((0, 7), (0, 11)), methodSymbol.SelectionRange);
      Assert.Equal(new Range((0, 0), (0, 13)), methodSymbol.Range);
      Assert.Equal(SymbolKind.Method, methodSymbol.Kind);
    }

    [Fact]
    public async Task CanResolveSymbolsForFunctionWithoutBody() {
      var source = "function ConstOne(): int";
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);

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
