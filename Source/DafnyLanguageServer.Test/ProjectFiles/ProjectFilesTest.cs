using System.IO;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Microsoft.Dafny.LanguageServer.Workspace;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Xunit;
using Xunit.Abstractions;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest; 

public class ProjectFilesTest : ClientBasedLanguageServerTest {

  [Fact]
  public async Task ProjectFileByItselfHasNoDiagnostics() {
    var tempDirectory = Path.GetRandomFileName();
    await CreateAndOpenTestDocument("", Path.Combine(tempDirectory, DafnyProject.FileName));
    await AssertNoDiagnosticsAreComing(CancellationToken);
  }

  [Fact]
  public async Task ProjectFileChangesArePickedUpAfterCacheExpiration() {
    await SetUp(options => options.WarnShadowing = false);
    var tempDirectory = Path.Combine(Path.GetTempPath(), Path.GetRandomFileName());
    Directory.CreateDirectory(tempDirectory);
    var projectFilePath = Path.Combine(tempDirectory, DafnyProject.FileName);
    await File.WriteAllTextAsync(projectFilePath, "");

    var source = @"
method Foo() {
  var x := 3;
  if (true) {
    var x := 4;
  }
}
";
    var documentItem = CreateTestDocument(source, Path.Combine(tempDirectory, "source.dfy"));
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
    await AssertNoDiagnosticsAreComing(CancellationToken);

    var warnShadowingOn = @"
[options]
warn-shadowing = true";

    await FileTestExtensions.WriteWhenUnlocked(projectFilePath, warnShadowingOn);
    await Task.Delay(ProjectManagerDatabase.ProjectFileCacheExpiryTime);
    ApplyChange(ref documentItem, new Range(0, 0, 0, 0), "//touch comment\n");
    var diagnostics = await GetLastDiagnostics(documentItem, CancellationToken);

    Assert.Single(diagnostics);
    Assert.Equal("Shadowed local-variable name: x", diagnostics[0].Message);
  }

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
    await SetUp(options => {
      options.Set(Function.FunctionSyntaxOption, "3");
      options.Set(CommonOptionBag.WarnShadowing, true);
    });
    var filePath = Path.Combine(Directory.GetCurrentDirectory(), "ProjectFiles/TestFiles/noWarnShadowing.dfy");
    var source = await File.ReadAllTextAsync(filePath);
    source += "\nghost function Bar(): int { 3 }";

    var doc1 = await CreateAndOpenTestDocument(source, "orphaned");
    var diagnostics1 = await GetLastDiagnostics(doc1, CancellationToken);
    Assert.Single(diagnostics1); // Stops after parsing
    await CreateAndOpenTestDocument(source, filePath);
    await AssertNoDiagnosticsAreComing(CancellationToken);
  }

  [Fact]
  public async Task FileOnlyAttachedToProjectFileThatAppliesToIt() {
    await SetUp(options => options.WarnShadowing = false);

    var projectFileSource = @"
[options]
warn-shadowing = true
";
    var directory = Path.Combine(Path.GetTempPath(), Path.GetRandomFileName());
    var outerProjectFile = CreateTestDocument(projectFileSource, Path.Combine(directory, DafnyProject.FileName));
    await client.OpenDocumentAndWaitAsync(outerProjectFile, CancellationToken);

    var innerProjectFile = CreateTestDocument("includes = []", Path.Combine(directory, "nested", DafnyProject.FileName));
    await client.OpenDocumentAndWaitAsync(innerProjectFile, CancellationToken);

    var filePath = Path.Combine(Directory.GetCurrentDirectory(), "ProjectFiles/TestFiles/noWarnShadowing.dfy");
    var source = await File.ReadAllTextAsync(filePath);
    var documentItem = CreateTestDocument(source, Path.Combine(directory, "nested/A.dfy"));
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
    var diagnostics = await GetLastDiagnostics(documentItem, CancellationToken);
    Assert.Single(diagnostics);
    Assert.Contains("Shadowed", diagnostics[0].Message);
  }

  [Fact]
  public async Task InMemoryProjectFileOverridesOptions() {
    await SetUp(options => options.WarnShadowing = false);

    var projectFileSource = @"
[options]
warn-shadowing = true
";
    var directory = Path.Combine(Path.GetTempPath(), Path.GetRandomFileName());
    var projectFile = CreateTestDocument(projectFileSource, Path.Combine(directory, DafnyProject.FileName));
    await client.OpenDocumentAndWaitAsync(projectFile, CancellationToken);

    var filePath = Path.Combine(Directory.GetCurrentDirectory(), "ProjectFiles/TestFiles/noWarnShadowing.dfy");
    var source = await File.ReadAllTextAsync(filePath);
    var documentItem = CreateTestDocument(source, Path.Combine(directory, "A.dfy"));
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
    var diagnostics = await GetLastDiagnostics(documentItem, CancellationToken);
    Assert.Single(diagnostics);
    Assert.Contains("Shadowed", diagnostics[0].Message);
  }

  public ProjectFilesTest(ITestOutputHelper output) : base(output) {
  }
}