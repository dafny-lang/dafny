using System.Collections.Generic;
using System.Collections.Immutable;
using System.IO;
using System.Linq;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using OmniSharp.Extensions.LanguageServer.Protocol.Workspace;
using Xunit;
using Xunit.Abstractions;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Lookup {

  public class WorkspaceSymbolTest : ClientBasedLanguageServerTest {

    [Fact]
    public async Task WorkspaceSymbolsAcrossFiles() {
      var cwd = Directory.GetCurrentDirectory();
      // These tests are not inlined since a later test uses only "includes-foo.dfy", but not
      // "defines-foo.dfy" but relies on the former existing. This would complicate
      // the test setup when inlining the file contents.
      var pathA = Path.Combine(cwd, "Lookup/TestFiles/defines-foo.dfy");
      var pathB = Path.Combine(cwd, "Lookup/TestFiles/includes-foo.dfy");
      var documentItemA = CreateTestDocument(await File.ReadAllTextAsync(pathA), pathA);
      var documentItemB = CreateTestDocument(await File.ReadAllTextAsync(pathB), pathB);

      await client.OpenDocumentAndWaitAsync(documentItemA, CancellationToken);
      await client.OpenDocumentAndWaitAsync(documentItemB, CancellationToken);

      var matchesFo = await client.RequestWorkspaceSymbols(
        new WorkspaceSymbolParams {
          Query = "fo"
        }
      );
      Assert.Single(matchesFo);
      Assert.Contains(matchesFo, si => si.Name == "foo" &&
                                       si.Kind == SymbolKind.Method &&
                                       si.Location.Uri.ToString().EndsWith("defines-foo.dfy"));

      var matchesBar = await client.RequestWorkspaceSymbols(
        new WorkspaceSymbolParams {
          Query = "bar"
        });
      Assert.Single(matchesBar);
      Assert.Contains(matchesBar, si => si.Name == "bar" &&
                                        si.Kind == SymbolKind.Method &&
                                        si.Location.Uri.ToString().EndsWith("includes-foo.dfy"));
    }

    [Fact]
    public async Task AllRelevantSymbolKindsDetected() {
      var documentItem = await GetDocumentItem(@"
class TestClass {}

module TestModule {}

function TestFunction(): int { 42 }

method TestMethod() returns (x: int) {
  x := 42;
}

datatype TestDatatype = TestConstructor

trait TestTrait {}

predicate TestPredicate { false }", "test-workspace-symbols.dfy", false);

      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);

      var testSymbols = new List<string> {
        "TestClass",
        "TestModule",
        "TestFunction",
        "TestDatatype",
        "TestConstructor",
        "TestTrait",
        "TestPredicate",
      };

      var response = await client.RequestWorkspaceSymbols(new WorkspaceSymbolParams {
        Query = "test"
      });
      foreach (var testSymbol in testSymbols) {
        Assert.True(response.Any(symbol => symbol.Name.Contains(testSymbol)),
          $"Could not find {testSymbol}");
      }
    }

    [Fact]
    public async Task SymbolImportedFromUnopenedFileDetected() {
      var cwd = Directory.GetCurrentDirectory();
      var path = Path.Combine(cwd, "Lookup/TestFiles/includes-foo.dfy");
      var documentItem = CreateTestDocument(await File.ReadAllTextAsync(path), path);

      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);

      var response = await client.RequestWorkspaceSymbols(new WorkspaceSymbolParams {
        Query = "foo"
      });
      Assert.Single(response);
      Assert.Contains(response, symbol => symbol.Name == "foo" &&
                                        symbol.Location.Uri.ToString().EndsWith("defines-foo.dfy"));
    }

    [Fact]
    public async Task TwoMatchesOrderedCorrectly() {
      var documentItem = await GetDocumentItem(@"method longerNameWithFooInIt() returns (x: int) {
    x := 42;
}

method prefixFoo() returns (x: int) {
    x := 23;
}", "multiple-matches.dfy", false);


      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);

      var response = await client.RequestWorkspaceSymbols(new WorkspaceSymbolParams {
        Query = "foo"
      });
      var items = response.ToImmutableList();
      Assert.Equal(2, response.Count());
      Assert.Contains("prefixFoo", items[0].Name);
      Assert.Contains("longerNameWithFooInIt", items[1].Name);
    }

    public WorkspaceSymbolTest(ITestOutputHelper output) : base(output) {
    }

  }
}