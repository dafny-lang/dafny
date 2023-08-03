using System;
using System.IO;
using System.Linq;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Xunit;
using Xunit.Abstractions;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Refactoring {
  public class RenameTest : ClientBasedLanguageServerTest {
    [Fact]
    public void ImplicitProjectFails() {
      // TODO
      Assert.True(false);
    }

    [Fact]
    public async Task InvalidNewNameIsNoOp() {
      var documentItem = await CreateAndOpenTestDocument("");
      var workspaceEdit = await RequestRename(documentItem, new Position(0, 0), "");
      Assert.Null(workspaceEdit);
    }

    [Fact]
    public async Task RenameDeclarationRenamesUsages() {
      var source = @"
const [>><i<] := 0
method M() {
  print [>i<] + [>i<];
}
".TrimStart();

      await SetUp(o => { });
      var tempDir = await SetUpProjectFile();
      await AssertRangesRenamed(source, tempDir, "foobar");
    }

    [Fact]
    public async Task RenameUsageRenamesDeclaration() {
      var source = @"
method [>foobar<]()
method U() { [>><foobar<](); }
".TrimStart();

      await SetUp(o => { });
      var tempDir = await SetUpProjectFile();
      await AssertRangesRenamed(source, tempDir, "M");
    }

    [Fact]
    public async Task RenameUsageRenamesOtherUsages() {
      var source = @"
module [>A<] {}
module B { import [>A<] }
module C { import [>><A<] }
module D { import [>A<] }
".TrimStart();

      await SetUp(o => { });
      var tempDir = await SetUpProjectFile();
      await AssertRangesRenamed(source, tempDir, "AAA");
    }

    [Fact]
    public void RenameDeclarationAcrossFiles() {
      // TODO
      Assert.True(false);
    }

    [Fact]
    public void RenameUsageAcrossFiles() {
      // TODO
      Assert.True(false);
    }

    /// <summary>
    /// Create an empty project file in a new temporary directory, and return the temporary directory's path.
    /// </summary>
    protected async Task<string> SetUpProjectFile() {
      var tempDir = Path.Combine(Path.GetTempPath(), Path.GetRandomFileName());
      Directory.CreateDirectory(tempDir);
      var projectFilePath = Path.Combine(tempDir, DafnyProject.FileName);
      await File.WriteAllTextAsync(projectFilePath, "");
      return tempDir;
    }

    protected override Task SetUp(Action<DafnyOptions> modifyOptions) {
      return base.SetUp(o => {
        o.Set(ServerCommand.ProjectMode, true);
        modifyOptions?.Invoke(o);
      });
    }

    /// <summary>
    /// Assert that after requesting a rename to <paramref name="newName"/> at the markup position,
    /// all markup ranges are renamed.
    /// </summary>
    private async Task AssertRangesRenamed(string source, string tempDir, string newName) {
      MarkupTestFile.GetPositionAndRanges(source, out var cleanSource,
        out var position, out var ranges);
      Assert.NotEmpty(ranges);

      var documentItem = await CreateAndOpenTestDocument(cleanSource, Path.Combine(tempDir, "tmp.dfy"));
      var workspaceEdit = await RequestRename(documentItem, position, newName);
      Assert.NotNull(workspaceEdit.Changes);
      Assert.Contains(documentItem.Uri, workspaceEdit.Changes);
      var editedText = DocumentEdits.ApplyEdits(workspaceEdit.Changes[documentItem.Uri], documentItem.Text);

      var expectedChanges = ranges.Select(range => new TextEdit {
        Range = range,
        NewText = newName,
      });
      var expectedText = DocumentEdits.ApplyEdits(expectedChanges, documentItem.Text);

      Assert.Equal(expectedText, editedText);
    }

    private async Task<WorkspaceEdit> RequestRename(string source, string newName) {
      MarkupTestFile.GetPositionAndRanges(source, out var cleanSource,
        out var position, out var ranges);

      var documentItem = await CreateAndOpenTestDocument(cleanSource);
      return await RequestRename(documentItem, position, newName);
    }

    private async Task<WorkspaceEdit> RequestRename(
      TextDocumentItem documentItem, Position position, string newName) {
      await AssertNoResolutionErrors(documentItem);
      return await client.RequestRename(
        new RenameParams {
          TextDocument = documentItem.Uri,
          Position = position,
          NewName = newName,
        }, CancellationToken);
    }

    public RenameTest(ITestOutputHelper output) : base(output) {
    }
  }
}
