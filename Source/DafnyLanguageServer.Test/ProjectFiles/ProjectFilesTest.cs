using System;
using System.IO;
using System.Linq;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Microsoft.Dafny.LanguageServer.Workspace;
using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Xunit;
using Xunit.Abstractions;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest;

public class ProjectFilesTest : ClientBasedLanguageServerTest {

  [Fact]
  public async Task ProducerLibrary() {
    var libraryDirectory = GetFreshTempPath();
    var producerSource = @"
module Producer {
  const x := 3
}".TrimStart();
    Directory.CreateDirectory(libraryDirectory);
    var producerPath = Path.Combine(libraryDirectory, "producer.dfy").Replace("\\", "/");
    await File.WriteAllTextAsync(producerPath, producerSource);
    var consumerSource = @"
module Consumer {
  import opened Producer
  const y := x + 2
}".TrimStart();

    var projectFileSource = $@"
[options]
library = [""{producerPath}""]".TrimStart();

    var consumerDirectory = GetFreshTempPath();
    Directory.CreateDirectory(consumerDirectory);
    await File.WriteAllTextAsync(Path.Combine(consumerDirectory, "consumer.dfy"), consumerSource);
    var projectFile = await CreateOpenAndWaitForResolve(projectFileSource, Path.Combine(consumerDirectory, DafnyProject.FileName));

    var diagnostics = await GetLastDiagnostics(projectFile);
    Assert.Single(diagnostics);
    Directory.Delete(libraryDirectory, true);
    Directory.Delete(consumerDirectory, true);
  }

  /// <summary>
  /// Previously this could cause two project managers for the same project to be created.
  /// </summary>
  [Fact]
  public async Task OpenTwoFilesThenIntroduceProjectFile() {
    var tempDirectory = Path.GetRandomFileName();
    var producerMarkup = @"
module [>Producer<]Oops {
  const x := 3
}".TrimStart();
    MarkupTestFile.GetPositionsAndRanges(producerMarkup, out var producerSource, out _, out var ranges);
    var producer = await CreateOpenAndWaitForResolve(producerSource, Path.Combine(tempDirectory, "producer.dfy"));
    var consumerSourceMarkup = @"
include ""producer.dfy""
module Consumer {
  import opened Pro><ducer
  const y := x + 2
}".TrimStart();
    MarkupTestFile.GetPositionAndRanges(consumerSourceMarkup, out var consumerSource, out var gotoPosition, out _);
    var consumer = await CreateOpenAndWaitForResolve(consumerSource, Path.Combine(tempDirectory, "consumer.dfy"));
    await CreateOpenAndWaitForResolve("", Path.Combine(tempDirectory, DafnyProject.FileName));
    // Let consumer.dfy realize it has a new project file 
    var definition1 = await RequestDefinition(consumer, gotoPosition);
    Assert.Empty(definition1);
    ApplyChange(ref producer, new Range(0, 15, 0, 19), ""); // Delete oops
    // Check that the project manager of consumer.dfy has incorporated the update in producer.dfy
    var definition2 = await RequestDefinition(consumer, gotoPosition);
    Assert.Single(definition2);
    Assert.Equal(ranges[0], definition2.First().Location!.Range);
  }

  [Fact]
  public async Task ProjectFileByItselfDiagnostics() {
    var tempDirectory = Path.GetRandomFileName();
    var projectFile = await CreateOpenAndWaitForResolve("", Path.Combine(tempDirectory, DafnyProject.FileName));
    var diagnostics = await diagnosticsReceiver.AwaitNextDiagnosticsAsync(CancellationToken);
    var errors = diagnostics.Where(d => d.Severity == DiagnosticSeverity.Error).ToList();
    Assert.Single(errors);
    Assert.Equal("no Dafny source files were specified as input", errors.First().Message);
  }

  [Fact]
  public async Task ProjectFileChangesArePickedUpAfterCacheExpiration() {
    const int cacheExpiry = 1000;
    await SetUp(options => {
      options.WarnShadowing = false;
      options.Set(CachingProjectFileOpener.ProjectFileCacheExpiry, cacheExpiry);
    });
    var tempDirectory = GetFreshTempPath();
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
    await AssertNoDiagnosticsAreComing(CancellationToken, documentItem);

    var warnShadowingOn = @"
[options]
warn-shadowing = true";

    await FileTestExtensions.WriteWhenUnlocked(projectFilePath, warnShadowingOn);
    ApplyChange(ref documentItem, new Range(0, 0, 0, 0), "//touch comment\n");
    await AssertNoDiagnosticsAreComing(CancellationToken);
    await Task.Delay(cacheExpiry);
    ApplyChange(ref documentItem, new Range(0, 0, 0, 0), "//touch comment\n");
    var diagnostics = await GetLastDiagnostics(documentItem);

    Assert.Single(diagnostics);
    Assert.Equal("Shadowed local-variable name: x", diagnostics[0].Message);
    Directory.Delete(tempDirectory, true);
  }

  [Fact]
  public async Task ClosestProjectFileIsFound() {
    var filePath = Path.Combine(Directory.GetCurrentDirectory(), "ProjectFiles/TestFiles/Nesting/src/foo.dfy");
    var source = await File.ReadAllTextAsync(filePath);
    var documentItem = CreateTestDocument(source, filePath);
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
    var diagnostics = await GetLastDiagnostics(documentItem);

    Assert.Single(diagnostics);
    Assert.Equal("Shadowed local-variable name: x", diagnostics[0].Message);
  }

  [Fact]
  public async Task ProjectFileOverridesOptions() {
    await SetUp(options => {
      options.Set(Function.FunctionSyntaxOption, "3");
      options.Set(CommonOptionBag.QuantifierSyntax, QuantifierSyntaxOptions.Version3);
      options.Set(CommonOptionBag.WarnShadowing, true);
    });
    var source = @"
method Foo() {
  var x := 3;
  if (true) {
    var x := 4;
  }
}

function Zoo(): set<(int,int)> {
  set x: int | 0 <= x < 5, y | 0 <= y < 6 :: (x,y)
}

ghost function Bar(): int { 3 }".TrimStart();

    var projectFileSource = @"
includes = [""**/*.dfy""]

[options]
warn-shadowing = false
quantifier-syntax = 4
function-syntax = 4";

    var directory = GetFreshTempPath();
    Directory.CreateDirectory(directory);

    var noProjectFile = await CreateOpenAndWaitForResolve(source, "orphaned.dfy");
    var diagnostics1 = await GetLastDiagnostics(noProjectFile);
    Assert.Single(diagnostics1); // Stops after parsing

    await File.WriteAllTextAsync(Path.Combine(directory, DafnyProject.FileName), projectFileSource);
    var sourceFile = await CreateOpenAndWaitForResolve(source, Path.Combine(directory, "source.dfy"));
    var diagnostics2 = await GetLastDiagnostics(sourceFile);
    Assert.Empty(diagnostics2.Where(d => d.Severity == DiagnosticSeverity.Error));
    Directory.Delete(directory, true);
  }

  [Fact]
  public async Task FileOnlyAttachedToProjectFileThatIncludesIt() {
    await SetUp(options => options.WarnShadowing = false);

    var outerSource = @"
[options]
warn-shadowing = true
";
    var directory = GetFreshTempPath();
    var outerProjectFile = CreateTestDocument(outerSource, Path.Combine(directory, DafnyProject.FileName));
    await client.OpenDocumentAndWaitAsync(outerProjectFile, CancellationToken);

    var innerDirectory = Path.Combine(directory, "nested");
    var innerProjectFile = CreateTestDocument("includes = []", Path.Combine(innerDirectory, DafnyProject.FileName));
    await client.OpenDocumentAndWaitAsync(innerProjectFile, CancellationToken);

    var source = @"
method Foo() {
  var x := 3;
  if (true) {
    var x := 4;
    var y: int := true; 
  }
}
";
    var documentItem = CreateTestDocument(source, Path.Combine(innerDirectory, "A.dfy"));
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
    var diagnostics = await GetLastDiagnostics(documentItem);
    Assert.Equal(2, diagnostics.Length);
    Assert.Contains(diagnostics, d => d.Message.Contains("Shadowed"));
  }

  [Fact]
  public async Task InMemoryProjectFileOverridesOptions() {
    await SetUp(options => options.WarnShadowing = false);

    var projectFileSource = @"
[options]
warn-shadowing = true
";
    var directory = GetFreshTempPath();
    var projectFile = CreateTestDocument(projectFileSource, Path.Combine(directory, DafnyProject.FileName));
    await client.OpenDocumentAndWaitAsync(projectFile, CancellationToken);

    var filePath = Path.Combine(Directory.GetCurrentDirectory(), "ProjectFiles/TestFiles/noWarnShadowing.dfy");
    var source = await File.ReadAllTextAsync(filePath);
    var documentItem = CreateTestDocument(source, Path.Combine(directory, "A.dfy"));
    await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
    var diagnostics = await GetLastDiagnostics(documentItem);
    Assert.Single(diagnostics);
    Assert.Contains("Shadowed", diagnostics[0].Message);
  }

  public ProjectFilesTest(ITestOutputHelper output) : base(output) {
  }
}