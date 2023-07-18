using System.IO;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Microsoft.Dafny.LanguageServer.Workspace;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Xunit;
using Xunit.Abstractions;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.ProjectFiles; 

public class CompetingProjectFilesTest : ClientBasedLanguageServerTest {

  /// <summary>
  /// A project should only publish diagnostics for uris which it owns,
  /// We can have a function filterOwnership(IdeState -> IdeState)
  /// that adds the "an error occurred outside this project"
  /// </summary>
  [Fact(Skip = "Not yet supported")]
  public async Task ProjectFileDoesNotOwnAllSourceFilesItUses() {
    var tempDirectory = Path.Combine(Path.GetTempPath(), Path.GetRandomFileName());
    var nestedDirectory = Path.Combine(tempDirectory, "nested");
    Directory.CreateDirectory(nestedDirectory);
    await File.WriteAllTextAsync(Path.Combine(nestedDirectory, "source.dfy"), "hasErrorInSyntax");
    await File.WriteAllTextAsync(Path.Combine(nestedDirectory, DafnyProject.FileName), "");

    var outerProject = CreateTestDocument("", Path.Combine(tempDirectory, DafnyProject.FileName));
    await client.OpenDocumentAndWaitAsync(outerProject, CancellationToken);

    var diagnostics = await GetLastDiagnostics(outerProject, CancellationToken);
    Assert.Single(diagnostics);
    Assert.Contains("something about a file not owned by the project", diagnostics[0].Message);
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
  [Fact(Skip = "Not yet supported")]
  public async Task NewProjectFileGrabsSourceFileOwnership() {
    var tempDirectory = Path.Combine(Path.GetTempPath(), Path.GetRandomFileName());
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

    var diagnostics0 = await GetLastDiagnostics(sourceFile, CancellationToken);
    Assert.Single(diagnostics0);
    Assert.Contains("Shadowed", diagnostics0[0].Message);

    await File.WriteAllTextAsync(Path.Combine(nestedDirectory, DafnyProject.FileName), "");
    ApplyChange(ref sourceFile, new Range(0, 0, 0, 0), "//comment\n");
    var diagnostics1 = await GetLastDiagnostics(sourceFile, CancellationToken);
    Assert.Empty(diagnostics1);
  }

  public CompetingProjectFilesTest(ITestOutputHelper output) : base(output) {
  }
}