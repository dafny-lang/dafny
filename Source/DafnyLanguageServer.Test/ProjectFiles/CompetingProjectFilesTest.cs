using System;
using System.IO;
using System.Linq;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Microsoft.Dafny.LanguageServer.Workspace;
using Microsoft.Extensions.Logging;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Xunit;
using Xunit.Abstractions;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.ProjectFiles;

public class CompetingProjectFilesTest : ClientBasedLanguageServerTest {


  /// <summary>
  /// A project should only publish diagnostics for uris which it owns,
  /// We can have a function filterOwnership(IdeState -> IdeState)
  /// that adds the "an error occurred outside this project"
  /// </summary>
  [Fact]
  public async Task ProjectFileDoesNotOwnAllSourceFilesItUses() {
    var tempDirectory = GetFreshTempPath();
    var nestedDirectory = Path.Combine(tempDirectory, "nested");
    Directory.CreateDirectory(nestedDirectory);
    await File.WriteAllTextAsync(Path.Combine(nestedDirectory, "source.dfy"), "hasErrorInSyntax");
    await File.WriteAllTextAsync(Path.Combine(nestedDirectory, DafnyProject.FileName), "");

    var project = await CreateOpenAndWaitForResolve("", Path.Combine(tempDirectory, DafnyProject.FileName));

    var diagnostics = await GetLastDiagnostics(project);
    var errors = diagnostics.Where(d => d.Severity == DiagnosticSeverity.Error).ToList();
    Assert.Single(errors);
    Assert.Contains("but is part of a different project", errors[0].Message);
    Directory.Delete(tempDirectory, true);
  }

  public readonly string hasShadowingSource = @"
method Foo() {
  var x := 3;
  if (true) {
    var x := 4;
  }
}".TrimStart();

  /// <summary>
  /// Here the outer project loses ownership of this document.
  /// At this point we simply need to apply the filterOwnership function on its last published IdeState again
  /// </summary>
  [Fact]
  public async Task NewProjectFileGrabsSourceFileOwnership() {
    var tempDirectory = GetFreshTempPath();
    var nestedDirectory = Path.Combine(tempDirectory, "nested");
    Directory.CreateDirectory(nestedDirectory);
    var sourceFilePath = Path.Combine(nestedDirectory, "source.dfy");

    var warnsShadowingProject = @"
[options]
warn-shadowing = true
".TrimStart();
    var outerProject = CreateTestDocument(warnsShadowingProject, Path.Combine(tempDirectory, DafnyProject.FileName));
    await client.OpenDocumentAndWaitAsync(outerProject, CancellationToken);

    var sourceFile = CreateTestDocument(hasShadowingSource, sourceFilePath);
    await client.OpenDocumentAndWaitAsync(sourceFile, CancellationToken);

    var diagnostics0 = await GetLastDiagnostics(sourceFile);
    Assert.Single(diagnostics0);
    Assert.Contains("Shadowed", diagnostics0[0].Message);

    await File.WriteAllTextAsync(Path.Combine(nestedDirectory, DafnyProject.FileName), "");

    ApplyChange(ref sourceFile, new Range(0, 0, 0, 0), "//comment\n");
    var diagnostics1 = await GetLastDiagnostics(sourceFile);
    Assert.Empty(diagnostics1);
    Directory.Delete(tempDirectory, true);
  }

  public CompetingProjectFilesTest(ITestOutputHelper output) : base(output, LogLevel.Debug) {
  }
}