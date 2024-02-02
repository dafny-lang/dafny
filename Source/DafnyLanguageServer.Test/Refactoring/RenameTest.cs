using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.IO;
using System.Linq;
using System.Threading.Tasks;
using JetBrains.Annotations;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Xunit;
using Xunit.Abstractions;
using Range = OmniSharp.Extensions.LanguageServer.Protocol.Models.Range;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Refactoring {
  public class RenameTest : ClientBasedLanguageServerTest {
    [Fact]
    public async Task ImplicitProjectFails() {
      var source = @"
const i := 0
".TrimStart();

      var documentItem = await CreateOpenAndWaitForResolve(source);
      await Assert.ThrowsAnyAsync<Exception>(() => RequestRename(documentItem, new Position(0, 6), "j"));
    }

    [Fact]
    public async Task InvalidNewNameIsNoOp() {
      var documentItem = await CreateOpenAndWaitForResolve("");
      var workspaceEdit = await RequestRename(documentItem, new Position(0, 0), "");
      Assert.Null(workspaceEdit);
    }

    [Fact]
    public async Task RenameNonSymbolFails() {
      var tempDir = await SetUpProjectFile();
      var documentItem = await CreateOpenAndWaitForResolve("module Foo {}", Path.Combine(tempDir, "tmp.dfy"));
      var workspaceEdit = await RequestRename(documentItem, new Position(0, 6), "space");
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

      var tempDir = await SetUpProjectFile();
      await AssertRangesRenamed(source, tempDir, "foobar");
    }

    [Fact]
    public async Task RenameUsageRenamesDeclaration() {
      var source = @"
method [>foobar<]()
method U() { [>><foobar<](); }
".TrimStart();

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

      var tempDir = await SetUpProjectFile();
      await AssertRangesRenamed(source, tempDir, "AAA");
    }

    [Fact]
    public async Task RenameDeclarationAcrossFiles() {
      var sourceA = @"
module A {
  class [>><C<] {}
}
".TrimStart();
      var sourceB = @"
module B {
  import A
  method M(c: A.[>C<]) {}
}
".TrimStart();

      var tempDir = await SetUpProjectFile();
      await AssertRangesRenamed(new[] { sourceA, sourceB }, tempDir, "CCC");
    }

    [Fact]
    public async Task RenameUsageAcrossFiles() {
      var sourceA = @"
abstract module [>A<] {}
".TrimStart();
      var sourceB = @"
abstract module B { import [>><A<] }
".TrimStart();

      var tempDir = await SetUpProjectFile();
      await AssertRangesRenamed(new[] { sourceA, sourceB }, tempDir, "AAA");
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

    /// <summary>
    /// Assert that after requesting a rename to <paramref name="newName"/>
    /// at the markup position in <paramref name="source"/>
    /// (there must be exactly one markup position),
    /// all markup ranges are renamed.
    /// </summary>
    private async Task AssertRangesRenamed(string source, string tempDir, string newName) {
      await AssertRangesRenamed(new[] { source }, tempDir, newName);
    }

    private record DocPosRange(TextDocumentItem Document, [CanBeNull] Position Position, ImmutableArray<Range> Ranges);

    /// <summary>
    /// Assert that after requesting a rename to <paramref name="newName"/>
    /// at the markup position in <paramref name="sources"/>
    /// (there must be exactly one markup position among all sources),
    /// all markup ranges are renamed.
    /// </summary>
    private async Task AssertRangesRenamed(IEnumerable<string> sources, string tempDir, string newName) {
      var items = sources.Select(async (source, sourceIndex) => {
        MarkupTestFile.GetPositionsAndRanges(source, out var cleanSource,
          out var positions, out var ranges);
        var documentItem = await CreateOpenAndWaitForResolve(cleanSource, Path.Combine(tempDir, $"tmp{sourceIndex}.dfy"));
        Assert.InRange(positions.Count, 0, 1);
        return new DocPosRange(documentItem, positions.FirstOrDefault((Position)null), ranges);
      }).Select(task => task.Result).ToImmutableList();

      var itemWithPos = items.Single(item => item.Position != null);
      var workspaceEdit = await RequestRename(itemWithPos.Document, itemWithPos.Position, newName);
      Assert.NotNull(workspaceEdit.Changes);

      foreach (var (document, _, ranges) in items) {
        Assert.Contains(document.Uri, workspaceEdit.Changes);
        var editedText = DocumentEdits.ApplyEdits(workspaceEdit.Changes[document.Uri], document.Text);
        var expectedChanges = ranges.Select(range => new TextEdit {
          Range = range,
          NewText = newName,
        });
        var expectedText = DocumentEdits.ApplyEdits(expectedChanges, document.Text);
        Assert.Equal(expectedText, editedText);
      }
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
