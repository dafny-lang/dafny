using System;
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
      Assert.Contains(matchesFo, si => si.Name == "method foo() returns (x: int)" &&
                                       si.Kind == SymbolKind.Method &&
                                       si.Location.Uri.ToString().EndsWith("defines-foo.dfy"));

      var matchesBar = await client.RequestWorkspaceSymbols(
        new WorkspaceSymbolParams {
          Query = "bar"
        });
      Assert.Single(matchesBar);
      Assert.Contains(matchesBar, si => si.Name == "method bar() returns (x: int)" &&
                                        si.Kind == SymbolKind.Method &&
                                        si.Location.Uri.ToString().EndsWith("includes-foo.dfy"));
    }

    [Fact]
    public async Task AllRelevantSymbolKindsDetected() {
      var cwd = Directory.GetCurrentDirectory();
      var pathA = Path.Combine(cwd, "Lookup/TestFiles/test-workspace-symbols.dfy");
      var documentItemA = CreateTestDocument(await File.ReadAllTextAsync(pathA), pathA);

      await client.OpenDocumentAndWaitAsync(documentItemA, CancellationToken);

      var testSymbols = new List<string>();
      testSymbols.Add("TestClass");
      testSymbols.Add("TestModule");
      testSymbols.Add("TestFunction");
      testSymbols.Add("TestDatatype");
      testSymbols.Add("TestConstructor");
      testSymbols.Add("TestTrait");
      testSymbols.Add("TestPredicate");

      var response = await client.RequestWorkspaceSymbols(new WorkspaceSymbolParams {
        Query = "test"
      });
      foreach (var testSymbol in testSymbols) {
        Assert.True(response.Any(symb => symb.Name.Contains(testSymbol)),
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
      Assert.Contains(response, symb => symb.Name == "method foo() returns (x: int)" &&
                                        symb.Location.Uri.ToString().EndsWith("defines-foo.dfy"));
    }

    [Fact]
    public async Task TwoMatchesOrderedCorrectly() {
      var cwd = Directory.GetCurrentDirectory();
      var path = Path.Combine(cwd, "Lookup/TestFiles/multiple-matches.dfy");
      var documentItem = CreateTestDocument(await File.ReadAllTextAsync(path), path);

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