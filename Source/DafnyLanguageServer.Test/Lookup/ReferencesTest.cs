using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using Xunit;
using Xunit.Abstractions;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Lookup {
  public class ReferencesTest : ClientBasedLanguageServerTest {
    private async Task<LocationContainer> RequestReferences(
      TextDocumentItem documentItem, Position position, bool includeDeclaration = false) {
      // We don't want resolution errors, but other diagnostics (like a cyclic-include warning) are okay
      await AssertNoResolutionErrors(documentItem);

      return await client.RequestReferences(
        new ReferenceParams {
          TextDocument = documentItem.Uri,
          Position = position,
          Context = new ReferenceContext() {
            IncludeDeclaration = includeDeclaration
          }
        }, CancellationToken).AsTask();
    }

    /// <summary>
    /// Assert that when finding-references at each cursor position and each regular span,
    /// the client returns all ranges marked with regular spans.
    /// </summary>
    private async Task AssertReferences(string source, string fileName, bool includeDeclaration = false) {
      MarkupTestFile.GetPositionsAndRanges(
        source, out var cleanSource, out var explicitPositions, out var expectedRangesArray);
      var expectedRanges = new HashSet<Range>(expectedRangesArray);

      var positionsFromRanges = expectedRangesArray.SelectMany(r => new[] {
        r.Start,
        new Position(r.End.Line, r.End.Character-1) });
      var allPositions = explicitPositions.Concat(positionsFromRanges);

      var documentItem = CreateTestDocument(cleanSource, fileName);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await AssertNoResolutionErrors(documentItem);

      foreach (var position in allPositions) {
        var result = await RequestReferences(documentItem, position, includeDeclaration);
        var resultRanges = result.Select(location => location.Range).ToHashSet();
        Assert.Equal(expectedRanges, resultRanges);
      }
    }

    [Fact]
    public async Task UnusedModule() {
      var source = @"
module [>><C<] {}
".TrimStart();

      await AssertReferences(source, "ExportNamedImport.dfy", true);
    }

    [Fact]
    public async Task ExplicitTypeBoundVariableInLambda() {
      var source = @"
datatype ><C = Cons
method Foo() {
  var f := (x: [>C<]) => 3;
  var c: [>C<] := Cons;
}
".TrimStart();

      await AssertReferences(source, "ExportNamedImport.dfy");
    }

    [Fact]
    public async Task ExportNamedImport() {
      var source = @"
module Low {
  const x := 3
}

module High {
  import ><MyLow = Low

  export
    provides
      [>MyLow<]
}
".TrimStart();

      await AssertReferences(source, "ExportNamedImport.dfy");
    }

    [Fact]
    public async Task ExportNamelessImport() {
      var source = @"
module ><Low {
  const x := 3
}

module High {
  import [>Low<]

  export
    provides
      [>Low<]
}
".TrimStart();

      await AssertReferences(source, "ExportImport.dfy");
    }

    [Fact]
    public async Task AliasModuleDecl() {
      var source = @"
module ><ToAlias {
  const x := 3
}

module Aliaser {
  import Used = [>ToAlias<]
  import Unused = [>ToAlias<]

  const x := Used.x 
}
".TrimStart();

      await AssertReferences(source, "AliasModuleDecl.dfy");
    }

    [Fact]
    public async Task FunctionReturnTypeDatatype() {
      var source = @"
datatype ><Result<T, Error> = Ok(value: T) | Error(error: Error)
function Foo(): [>Result<]<int, int> {
  Ok(1)
}
".TrimStart();

      await AssertReferences(source, "FunctionReturnTypeDatatype.dfy");
    }

    [Fact]
    public async Task Const() {
      var source = @"
const ><c := 1
method M1() {
  print [>c<];
}
method M2() {
  print [>c<];
}
".TrimStart();

      await AssertReferences(source, "Const.dfy");
    }

    [Fact]
    public async Task Var() {
      var source = @"
method M() {
  var ><v := 1;
  print [>v<];
  print [>v<];
  var v2 := [>v<] + [>v<];
}
".TrimStart();

      await AssertReferences(source, "Var.dfy");
    }

    [Fact]
    public async Task Method() {
      var source = @"
method ><M1() {
}
method M2() {
  [>M1<]();
}
method M3() {
  [>M1<]();
}
".TrimStart();

      await AssertReferences(source, "Method.dfy");
    }

    [Fact]
    public async Task Parameter() {
      var source = @"
method M(><x: int) {
  print [>x<];
}
".TrimStart();

      await AssertReferences(source, "Parameter.dfy");
    }

    [Fact]
    public async Task Module() {
      var source = @"
module ><M1 {
}
module M2 {
  import [>M1<]
}
module M3 {
  import [>M1<]
}
module MR refines [>M1<] {}
".TrimStart();

      await AssertReferences(source, "Module.dfy");
    }

    // It seems that datatype declaration/usage information is not tracked
    [Fact(Skip = "Not implemented")]
    public async Task DatatypeDeclaration() {
      var source = @"
datatype ><D = D
method M(d: [>D<]) {
  print (match d
    case D => 1
  );
}
".TrimStart();

      await AssertReferences(source, "DatatypeDeclaration.dfy");
    }

    [Fact]
    public async Task DatatypeConstructor() {
      var source = @"
datatype Letter = ><A | B | C
method M(l: Letter) {
  print match l
    case [>A<] => 1
    case B => 2
    case C => 3
  ;
}
".TrimStart();

      await AssertReferences(source, "DatatypeConstructor.dfy");
    }

    [Fact]
    public async Task DatatypeDestructor() {
      var source = @"
datatype Option = None | Some(><value: int)
method M(o: Option) {
  print match o
    case None => 0
    case Some(value) => value + o.[>value<]
  ;
}
".TrimStart();

      await AssertReferences(source, "DatatypeDestructor.dfy");
    }

    // It seems that type declaration/usage information is not tracked
    [Fact(Skip = "Not implemented")]
    public async Task Type() {
      var source = @"
type ><T = int
method M(t: [>T<]) {}
".TrimStart();

      await AssertReferences(source, "Type.dfy");
    }

    // It seems that newtype declaration/usage information is not tracked
    [Fact(Skip = "Not implemented")]
    public async Task Newtype() {
      var source = @"
newtype ><T = int
method M(t: [>T<]) {}
".TrimStart();

      await AssertReferences(source, "Newtype.dfy");
    }

    [Fact]
    public async Task Trait() {
      var source = @"
trait ><T {}
class C extends [>T<] {}
".TrimStart();

      await AssertReferences(source, "Trait.dfy");
    }

    // It seems that class declaration/usage information is not tracked
    [Fact(Skip = "Not implemented")]
    public async Task ClassDeclaration() {
      var source = @"
class ><C {}
method M(c: [>C<]) {}
".TrimStart();

      await AssertReferences(source, "ClassDeclaration.dfy");
    }

    [Fact]
    public async Task ClassField() {
      var source = @"
class C {
  var ><f: int
  constructor() { [>f<] := 0; }
}
method M(c: C) {
  print c.[>f<];
}
".TrimStart();

      await AssertReferences(source, "ClassField.dfy");
    }

    [Fact]
    public async Task ClassMethod() {
      var source = @"
class C {
  method ><CM() {}
}
method M(c: C) {
  c.[>CM<]();
}
".TrimStart();

      await AssertReferences(source, "ClassMethod.dfy");
    }

    [Fact]
    public async Task AcrossFiles() {
      var cwd = Directory.GetCurrentDirectory();
      var pathA = Path.Combine(cwd, "Lookup/TestFiles/find-refs-a.dfy");
      var pathB = Path.Combine(cwd, "Lookup/TestFiles/find-refs-b.dfy");
      var documentItemA = CreateTestDocument(await File.ReadAllTextAsync(pathA), pathA);
      var documentItemB = CreateTestDocument(await File.ReadAllTextAsync(pathB), pathB);

      await client.OpenDocumentAndWaitAsync(documentItemA, CancellationToken);
      await client.OpenDocumentAndWaitAsync(documentItemB, CancellationToken);

      var expectedRef = new Location {
        Uri = DocumentUri.File(pathB),
        Range = new Range(2, 9, 2, 10),
      };

      var refFromA = (await RequestReferences(documentItemA, new Position(1, 7))).Single();
      Assert.Equal(expectedRef, refFromA);

      var refFromB = (await RequestReferences(documentItemB, new Position(2, 9))).Single();
      Assert.Equal(expectedRef, refFromB);
    }

    public ReferencesTest(ITestOutputHelper output) : base(output) {
    }
  }
}
