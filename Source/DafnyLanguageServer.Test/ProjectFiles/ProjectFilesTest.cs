using System.IO;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Xunit;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest; 

public class ProjectFilesTest : ClientBasedLanguageServerTest {
  [Fact]
  public async Task ClosestProjectFileIsFound() {
    var filePath = Path.Combine(Directory.GetCurrentDirectory(), "ProjectFiles/TestFiles/Nesting/src/foo.dfy");
    var source = await File.ReadAllTextAsync(filePath);
    var documentItem = CreateTestDocument(source, filePath);
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
    var diagnostics = await GetLastDiagnostics(documentItem, CancellationToken);

    Assert.Single(diagnostics);
    Assert.Equal("Shadowed local-variable name: x", diagnostics[0].Message);
  }

  [Fact]
  public async Task ProjectFileOverridesOptions() {
    await SetUp(options => options.WarnShadowing = true);
    var filePath = Path.Combine(Directory.GetCurrentDirectory(), "ProjectFiles/TestFiles/noWarnShadowing.dfy");
    var source = await File.ReadAllTextAsync(filePath);
    var documentItem = CreateTestDocument(source, filePath);
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
    var diagnostics = await GetLastDiagnostics(documentItem, CancellationToken);

    Assert.Empty(diagnostics);
  }
}