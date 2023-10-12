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
  public async Task ProjectFileErrorIsShown() {
    var projectFileSource = @"includes = [stringWithoutQuotes]";
    await CreateOpenAndWaitForResolve(projectFileSource, DafnyProject.FileName);
    var diagnostics = await diagnosticsReceiver.AwaitNextNotificationAsync(CancellationToken);
    Assert.Equal(2, diagnostics.Diagnostics.Count());
    Assert.Equal(new Range(0, 0, 0, 0), diagnostics.Diagnostics.First().Range);
    Assert.Contains("contains the following errors", diagnostics.Diagnostics.First().Message);
  }

  [Fact]
  public async Task ProjectFileErrorIsShownFromDafnyFile() {
    var projectFileSource = @"includes = [stringWithoutQuotes]";
    var directory = Path.Combine(Path.GetTempPath(), Path.GetRandomFileName());
    Directory.CreateDirectory(directory);
    var projectFilePath = Path.Combine(directory, DafnyProject.FileName);
    await File.WriteAllTextAsync(projectFilePath, projectFileSource);
    await CreateOpenAndWaitForResolve("method Foo() { }", Path.Combine(directory, "ProjectFileErrorIsShownFromDafnyFile.dfy"));
    var diagnostics = await diagnosticsReceiver.AwaitNextNotificationAsync(CancellationToken);
    Assert.Equal(DocumentUri.File(projectFilePath), diagnostics.Uri.GetFileSystemPath());
    Assert.Equal(2, diagnostics.Diagnostics.Count());
    Assert.Equal(new Range(0, 0, 0, 0), diagnostics.Diagnostics.First().Range);
    Assert.Contains("contains the following errors", diagnostics.Diagnostics.First().Message);
    Assert.Equal(@"Files referenced by project are:
ProjectFileErrorIsShownFromDafnyFile.dfy", diagnostics.Diagnostics.ElementAt(1).Message);
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
    await Task.Delay(ProjectManagerDatabase.ProjectFileCacheExpiryTime);
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
    Assert.Single(diagnostics);
    Assert.Equal("Project references no files", diagnostics.First().Message);
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
    await AssertNoDiagnosticsAreComing(CancellationToken, documentItem);

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

    var directory = Path.Combine(Path.GetTempPath(), Path.GetRandomFileName());
    Directory.CreateDirectory(directory);

    var noProjectFile = await CreateOpenAndWaitForResolve(source, "orphaned.dfy");
    var diagnostics1 = await GetLastDiagnostics(noProjectFile, CancellationToken);
    Assert.Single(diagnostics1); // Stops after parsing

    await File.WriteAllTextAsync(Path.Combine(directory, DafnyProject.FileName), projectFileSource);
    var sourceFile = await CreateOpenAndWaitForResolve(source, Path.Combine(directory, "source.dfy"));
    var diagnostics2 = await GetLastDiagnostics(sourceFile, CancellationToken);
    Assert.Empty(diagnostics2.Where(d => d.Severity == DiagnosticSeverity.Error));
  }

  [Fact]
  public async Task FileOnlyAttachedToProjectFileThatIncludesIt() {
    await SetUp(options => options.WarnShadowing = false);

    var outerSource = @"
[options]
warn-shadowing = true
";
    var directory = Path.Combine(Path.GetTempPath(), Path.GetRandomFileName());
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
  }
}
";
    var documentItem = CreateTestDocument(source, Path.Combine(innerDirectory, "A.dfy"));
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