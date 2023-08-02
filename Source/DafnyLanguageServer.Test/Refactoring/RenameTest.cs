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

      await AssertRangesRenamed(source, "foobar");
    }

    [Fact]
    public async Task RenameUsageRenamesDeclaration() {
      var source = @"
method [>foobar<]()
method U() { [>><foobar<](); }
".TrimStart();

      await AssertRangesRenamed(source, "M");
    }

    [Fact]
    public async Task RenameUsageRenamesOtherUsages() {
      var source = @"
module [>A<] {}
module B { import [>A<] }
module C { import [>><A<] }
module D { import [>A<] }
".TrimStart();

      await AssertRangesRenamed(source, "AAA");
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
    /// Assert that after requesting a rename to <paramref name="newName"/> at the markup position,
    /// all markup ranges are renamed.
    /// </summary>
    private async Task AssertRangesRenamed(string source, string newName) {
      MarkupTestFile.GetPositionAndRanges(source, out var cleanSource,
        out var position, out var ranges);
      Assert.NotEmpty(ranges);

      var documentItem = await CreateAndOpenTestDocument(cleanSource);
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
