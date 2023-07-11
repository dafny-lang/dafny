using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using OmniSharp.Extensions.LanguageServer.Protocol.Progress;
using Xunit;
using Xunit.Abstractions;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Lookup {
  public class ReferencesTest : ClientBasedLanguageServerTest {
    private IRequestProgressObservable<IEnumerable<Location>, LocationContainer> RequestReferences(
      TextDocumentItem documentItem, Position position) {
      return client.RequestReferences(
        new ReferenceParams {
          TextDocument = documentItem.Uri,
          Position = position
        }, CancellationToken);
    }

    /// <summary>
    /// Assert that when finding-references at each cursor position,
    /// the client returns all ranges marked with regular spans.
    /// </summary>
    /// <param name="source"></param>
    private async Task AssertReferences(string source) {
      MarkupTestFile.GetPositionsAndRanges(
        source, out var cleanSource, out var positions, out var expectedRangesArray);
      var expectedRanges = new HashSet<Range>(expectedRangesArray);

      var documentItem = CreateTestDocument(cleanSource);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);

      foreach (var position in positions) {
        var result = await RequestReferences(documentItem, position).AsTask();
        var resultRanges = result.Select(location => location.Range).ToHashSet();
        Assert.Equal(expectedRanges, resultRanges);
      }
    }

    [Fact]
    public async Task Const() {
      var source = @"
const ><c := 1
method M1() {
  print [>><c<];
}
method M2() {
  print [>c><<];
}
".TrimStart();

      await AssertReferences(source);
    }

    [Fact]
    public async Task Var() {
      var source = @"
method M() {
  var ><v := 1;
  print [>><v<];
  print [>><v<];
  var v2 := [>><v<] + [>><v<];
}
".TrimStart();

      await AssertReferences(source);
    }

    [Fact]
    public async Task Method() {
      var source = @"
method ><M1() {
}
method M2() {
  [>><M1<]();
}
method M3() {
  [>><M1<]();
}
".TrimStart();

      await AssertReferences(source);
    }

    [Fact]
    public async Task Parameter() {
      var source = @"
method M(><x: int) {
  print [>><x<];
}
".TrimStart();

      await AssertReferences(source);
    }

    [Fact]
    public async Task Module() {
      var source = @"
module ><M1 {
}
module M2 {
  import [>><M1<]
}
module M3 {
  import [>><M1<]
}
module MR refines [>><M1<] {}
".TrimStart();

      await AssertReferences(source);
    }

    // It seems that datatype declaration/usage information is not tracked
    [Fact(Skip = "Not implemented")]
    public async Task DatatypeDeclaration() {
      var source = @"
datatype ><D = D
method M(d: [>><D<]) {
  print (match d
    case D => 1
  );
}
".TrimStart();

      await AssertReferences(source);
    }

    [Fact]
    public async Task DatatypeConstructor() {
      var source = @"
datatype Letter = ><A | B | C
method M(l: Letter) {
  print match l
    case [>><A<] => 1
    case B => 2
    case C => 3
  ;
}
".TrimStart();

      await AssertReferences(source);
    }

    [Fact]
    public async Task DatatypeDestructor() {
      var source = @"
datatype Option = None | Some(><value: int)
method M(o: Option) {
  print match o
    case None => 0
    case Some(value) => value + o.[>><value<]
  ;
}
".TrimStart();

      await AssertReferences(source);
    }

    // It seems that type declaration/usage information is not tracked
    [Fact(Skip = "Not implemented")]
    public async Task Type() {
      var source = @"
type ><T = int
method M(t: [>><T<]) {}
".TrimStart();

      await AssertReferences(source);
    }

    // It seems that newtype declaration/usage information is not tracked
    [Fact(Skip = "Not implemented")]
    public async Task Newtype() {
      var source = @"
newtype ><T = int
method M(t: [>><T<]) {}
".TrimStart();

      await AssertReferences(source);
    }

    [Fact]
    public async Task Trait() {
      var source = @"
trait ><T {}
class C extends [>><T<] {}
".TrimStart();

      await AssertReferences(source);
    }

    // It seems that class declaration/usage information is not tracked
    [Fact(Skip = "Not implemented")]
    public async Task ClassDeclaration() {
      var source = @"
class ><C {}
method M(c: [>><C<]) {}
".TrimStart();

      await AssertReferences(source);
    }

    [Fact]
    public async Task ClassField() {
      var source = @"
class ><C {
  var f: int := 0
}
method M(c: C) {
  print c.[>><f<];
}
".TrimStart();

      await AssertReferences(source);
    }

    [Fact]
    public async Task ClassMethod() {
      var source = @"
class C {
  method ><CM() {}
}
method M(c: C) {
  c.[>><CM<]();
}
".TrimStart();

      await AssertReferences(source);
    }

    // TODO - not sure why both primary assertions are failing
    [Fact]
    public async Task AcrossFiles() {
      var sourceA = @"
include ""B.dfy""
module ><A {}
".TrimStart();
      var sourceB = @"
include ""A.dfy""
module B {
  import [>><A<]
}
".TrimStart();

      MarkupTestFile.GetPositionsAndRanges(
        sourceA, out var cleanSourceA, out var positionsA, out var rangesA);
      MarkupTestFile.GetPositionsAndRanges(
        sourceB, out var cleanSourceB, out var positionsB, out var rangesB);
      Assert.Single(positionsA);
      Assert.Single(positionsB);
      Assert.Single(rangesB);

      var cwd = Directory.GetCurrentDirectory();
      var pathA = Path.Combine(cwd, "Lookup/TestFiles/A.dfy");
      var pathB = Path.Combine(cwd, "Lookup/TestFiles/B.dfy");

      var documentItemA = CreateTestDocument(cleanSourceA, pathA);
      await client.OpenDocumentAndWaitAsync(documentItemA, CancellationToken);
      var refA = (await RequestReferences(documentItemA, positionsA.First()).AsTask()).Single();
      Assert.Equal(rangesB[0], refA.Range);

      // Shouldn't need both documents open
      await client.CloseDocumentAndWaitAsync(documentItemA, CancellationToken);

      var documentItemB = CreateTestDocument(cleanSourceB, pathB);
      await client.OpenDocumentAndWaitAsync(documentItemB, CancellationToken);
      var refB = (await RequestReferences(documentItemB, positionsB.First()).AsTask()).Single();
      Assert.Equal(rangesB[0], refB.Range);
    }

    public ReferencesTest(ITestOutputHelper output) : base(output) {
    }
  }
}
