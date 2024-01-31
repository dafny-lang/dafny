using System;
using System.IO;
using System.Linq;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Xunit;
using Xunit.Abstractions;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Synchronization;

public class ProjectFileDiagnosticsTest : ClientBasedLanguageServerTest {

  [Fact]
  public async Task ProjectFileErrorIsShown() {
    var projectFileSource = @"includes = [stringWithoutQuotes]";
    var projectFile = await CreateOpenAndWaitForResolve(projectFileSource, DafnyProject.FileName);
    var diagnostics = await GetLastDiagnostics(projectFile, DiagnosticSeverity.Error);
    Assert.Single(diagnostics);
    Assert.Equal(new Range(0, 0, 0, 0), diagnostics.First().Range);
    Assert.Contains("contains the following errors", diagnostics.First().Message);
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
    Assert.Contains(diagnostics.Diagnostics, d => d.Message.Contains("contains the following errors"));
    Assert.Contains(diagnostics.Diagnostics, d => d.Message.Contains($"Files referenced by project are:{Environment.NewLine}ProjectFileErrorIsShownFromDafnyFile.dfy"));
  }

  [Fact]
  public async Task IncludeNotFound() {
    var projectFile = @"
includes = [""doesNotExist.dfy""]
".TrimStart();

    var project = CreateAndOpenTestDocument(projectFile, DafnyProject.FileName);
    var diagnostics = await GetLastDiagnostics(project);
    Assert.Single(diagnostics);
    Assert.Contains("no Dafny source files were specified as input", diagnostics[0].Message);
  }

  [Fact]
  public async Task LibraryNotFound() {
    var projectFile = @"
[options]
library = [""doesNotExist.dfy""]
".TrimStart();

    var project = CreateAndOpenTestDocument(projectFile, DafnyProject.FileName);
    var diagnostics = await GetLastDiagnostics(project, DiagnosticSeverity.Error);
    Assert.Single(diagnostics);
    Assert.Contains("not found", diagnostics[0].Message);
  }

  public ProjectFileDiagnosticsTest(ITestOutputHelper output, LogLevel dafnyLogLevel = LogLevel.Information)
    : base(output, dafnyLogLevel) {
  }
}