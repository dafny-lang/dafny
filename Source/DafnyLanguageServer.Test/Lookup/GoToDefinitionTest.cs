using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.IO;
using System.Linq;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using Xunit;
using Xunit.Abstractions;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Lookup {
  public class GoToDefinitionTest : ClientBasedLanguageServerTest {

    [Fact]
    public async Task DatatypeFields() {
      var source = @"
datatype MultipleFields = MultipleFields(x: int, [>y<]: int)

method Update(m: MultipleFields) {
  var m2 := m.(><y := 3);
}".TrimStart();
      await AssertPositionsLineUpWithRanges(source);
    }

    [Fact]
    public async Task ModuleImport1ResolutionErrorInDependency() {
      var source = @"
module User {
 import Us><ed
 
 const x := Used.x
}

module [>Used<] {
  const x: bool := 3
}".TrimStart();
      await AssertPositionsLineUpWithRanges(source);
    }

    [Fact]
    public async Task ResolutionErrorInDependency() {
      var source = @"
module User {
 import Used
 
 const x := Used.><x
}

module [>Used<] {
  const x: bool := 3
}".TrimStart();
      MarkupTestFile.GetPositionsAndNamedRanges(source, out var cleanSource,
        out var positions, out var ranges);

      var documentItem = await CreateOpenAndWaitForResolve(cleanSource, null);
      foreach (var position in positions) {
        var result = (await RequestDefinition(documentItem, position));
        Assert.Empty(result);
      }
    }

    [Fact]
    public async Task ResolutionError() {
      var source = @"
module User {
 import Used
 
 const x: bool := Used.><x
}

module Used {
  const [>x<] := 3
}".TrimStart();
      await AssertPositionsLineUpWithRanges(source);
    }

    [Fact]
    public async Task ResolutionErrorInDependent() {
      var source = @"
module User {
 import Used
 
 const x: bool := Used.3
}

module Used {
  const [>y<] := 3
  const x: bool := ><y
}".TrimStart();
      await AssertPositionsLineUpWithRanges(source);
    }

    [Fact]
    public async Task ModuleImport1() {
      var source = @"
module User {
 import Us><ed
 
 const x := Used.x
}

module [>Used<] {
  const x := 3
}".TrimStart();
      await AssertPositionsLineUpWithRanges(source);
    }

    [Fact]
    public async Task ModuleImport2() {
      var source = @"
module User {
 import Used
 
 const x := Us><ed.x
}

module [>Used<] {
  const x := 3
}".TrimStart();
      await AssertPositionsLineUpWithRanges(source);
    }

    [Fact]
    public async Task ExplicitProjectToGoDefinitionWorks() {
      var sourceA = @"
const a := 3;
".TrimStart();

      var sourceB = @"
const b := a + 2;
".TrimStart();

      var directory = Path.GetRandomFileName();
      await CreateOpenAndWaitForResolve("", Path.Combine(directory, DafnyProject.FileName));
      var aFile = await CreateOpenAndWaitForResolve(sourceA, Path.Combine(directory, "A.dfy"));
      var bFile = await CreateOpenAndWaitForResolve(sourceB, Path.Combine(directory, "B.dfy"));

      var result1 = await RequestDefinition(bFile, new Position(0, 11));
      Assert.Equal(new Range(0, 6, 0, 7), result1.Single().Location!.Range);
    }

    [Fact]
    public async Task WhileLoop() {
      var source = @"
method HasLoop() {
  var x := 1;
  [>while<](true) {
    if (x > 2) {
      br><eak;
    }
    x := x + 1;
  }
}
".TrimStart();

      await AssertPositionsLineUpWithRanges(source);
    }

    [Fact]
    public async Task MatchExprAndMethodWithoutBody() {
      var source = @"  
datatype Option<+U> = {>0:None<} | Some(val: U) {

  function FMap<V>(f: U -> V): Option<V> {
    match this
    case None => N><one
    case Some(x) => Some(f(x))
  }
}

datatype A = A {
  static method create() returns (ret: A)
}
datatype Result<T, E> = Ok(value: T) | Err({>1:error<}: E) {
  function PropagateFailure<U>(): Result<U, E>
    requires Err?
  {
    Err(this.er><ror)
  }
}
".TrimStart();

      await AssertPositionsLineUpWithRanges(source);
    }

    [Fact]
    public async Task StaticFunctionCall() {
      var source = @"
module [>Zaz<] {
  trait [>E<] {
    static function [>Foo<](): E
  }
}

function Bar(): Zaz.E {
  Z><az.><E.F><oo()
}
".TrimStart();

      await AssertPositionsLineUpWithRanges(source);
    }

    [Fact]
    public async Task FunctionCallAndGotoOnDeclaration() {
      var source = @"
function [>Fibo><nacciSpec<](><n: nat): nat {
  if (n == 0) then 0
  else if (n == 1) then 1
  else Fi><bonacciSpec(n - 1) + FibonacciSpec(n - 2)
}

type seq31<[>T<]> = x: seq<><T> | 0 <= |x| <= 32 as int
".TrimStart();

      MarkupTestFile.GetPositionsAndRanges(source, out var cleanSource,
        out var positions, out var ranges);
      var documentItem = CreateTestDocument(cleanSource, "FunctionCallAndGotoOnDeclaration.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);

      var fibonacciSpecOnItself = (await RequestDefinition(documentItem, positions[0]));
      Assert.Single(fibonacciSpecOnItself);

      var nOnItself = (await RequestDefinition(documentItem, positions[1]));
      Assert.Single(nOnItself);

      var fibonacciCall = (await RequestDefinition(documentItem, positions[2])).Single();
      Assert.Equal(ranges[0], fibonacciCall.Location!.Range);

      var typeParameter = (await RequestDefinition(documentItem, positions[3])).Single();
      Assert.Equal(ranges[1], typeParameter.Location!.Range);
    }

    [Fact]
    public async Task DatatypesAndMatches() {
      var source = @"
datatype Identity<T> = [>Identity<](value: T)
datatype Colors = Red | [>Green<] | Blue

function Foo([>value<]: Identity<Colors>): bool {
  match va><lue {
    case Ide><ntity(Red()) => true
    case Identity(Gr><een) => false // Warning
    case Identity(Blue()) => false
  }
}

method Bar([>value<]: Identity<Colors>) returns (x: bool) {
  match v><alue {
    case Ide><ntity(Red()) => return true;
    case Identity(Gr><een) => return false; // Warning
    case Identity(Blue()) => return false;
  }
}
".TrimStart();

      MarkupTestFile.GetPositionsAndRanges(source, out var cleanSource,
        out var positions, out var ranges);
      var documentItem = CreateTestDocument(cleanSource, "DatatypesAndMatches.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var matchSource = (await RequestDefinition(documentItem, positions[0])).Single();
      Assert.Equal(ranges[2], matchSource.Location!.Range);

      var identity = (await RequestDefinition(documentItem, positions[1])).Single();
      Assert.Equal(new Range((0, 23), (0, 31)), identity.Location!.Range);

      var green = (await RequestDefinition(documentItem, positions[2])).Single();
      Assert.Equal(new Range((1, 24), (1, 29)), green.Location!.Range);

      var matchSourceStmt = (await RequestDefinition(documentItem, positions[3])).Single();
      Assert.Equal(ranges[3], matchSourceStmt.Location!.Range);

      var identityStmt = (await RequestDefinition(documentItem, positions[4])).Single();
      Assert.Equal(new Range((0, 23), (0, 31)), identityStmt.Location!.Range);

      var greenStmt = (await RequestDefinition(documentItem, positions[5])).Single();
      Assert.Equal(new Range((1, 24), (1, 29)), greenStmt.Location!.Range);
    }

    [Fact]
    public async Task JumpToExternModule() {
      var source = @"
module {:extern} [>Provider<] {
  newtype nat64 = x: int | 0 <= x <= 0xffff_ffff_ffff_ffff
  type [>usize<] = nat64
}

module Consumer {
  import opened P><rovider

  method DoIt() {
    var [>le><ngth<]: u><size := 3;
    le><ngth := 4;
  }
}".TrimStart();
      MarkupTestFile.GetPositionsAndRanges(source, out var cleanSource,
        out var positions, out var ranges);
      var documentItem = CreateTestDocument(cleanSource, "JumpToExternModule.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var usizeReference = (await RequestDefinition(documentItem, positions[2])).Single();
      Assert.Equal(documentItem.Uri, usizeReference.Location!.Uri);
      Assert.Equal(ranges[1], usizeReference.Location.Range);

      var lengthDefinition = (await RequestDefinition(documentItem, positions[1]));
      Assert.Single(lengthDefinition);

      var providerImport = (await RequestDefinition(documentItem, positions[0])).Single();
      Assert.Equal(ranges[0], providerImport.Location!.Range);

      var lengthAssignment = (await RequestDefinition(documentItem, positions[3])).Single();
      Assert.Equal(ranges[2], lengthAssignment.Location!.Range);
    }

    [Fact]
    public async Task JumpToOtherModule() {
      var source = @"
module {>2:Provider<} {
  class A {
    var [>x<]: int;

    constructor() {}

    function [>GetX<](): int
      reads this`><x
    {
      this.x
    }
  }
}

module Consumer {
  import opened Provider

  method DoIt() returns (x: int) {
    var a := new A();
    return a.G><etX();
  }
}

module Consumer2 {
  import Provider

  type A2 = Pro><vider.A
}".TrimStart();

      await AssertPositionsLineUpWithRanges(source);
    }

    [Fact]
    public async Task DefinitionOfMethodInvocationOfMethodDeclaredInSameDocumentReturnsLocation() {
      var source = @"
module Container {
  method GetIt() returns (x: int) {
  }

  method DoIt(arg: int) {
  }
}

method CallIts() returns () {
  var x := Container.GetIt();
  Container.DoIt(x);
}".TrimStart();
      var documentItem = CreateTestDocument(source, "DefinitionOfMethodInvocationOfMethodDeclaredInSameDocumentReturnsLocation.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);

      var containerReference = (await RequestDefinition(documentItem, (9, 11))).Single();
      Assert.Equal(new Range((0, 7), (0, 16)), containerReference.Location!.Range);

      var getItCall = (await RequestDefinition(documentItem, (9, 23))).Single();
      Assert.Equal(new Range((1, 9), (1, 14)), getItCall.Location!.Range);

      var doItCall = (await RequestDefinition(documentItem, (10, 12))).Single();
      Assert.Equal(new Range((4, 9), (4, 13)), doItCall.Location!.Range);

      var xVar = (await RequestDefinition(documentItem, (10, 17))).Single();
      Assert.Equal(new Range((9, 6), (9, 7)), xVar.Location!.Range);
    }

    [Fact]
    public async Task DefinitionReturnsBeforeVerificationIsComplete() {
      var documentItem = CreateTestDocument(NeverVerifies, "DefinitionReturnsBeforeVerificationIsComplete.dfy");
      client.OpenDocument(documentItem);
      var verificationTask = GetLastDiagnostics(documentItem);
      var definitionTask = RequestDefinition(documentItem, (4, 14));
      var first = await Task.WhenAny(verificationTask, definitionTask);
      Assert.False(verificationTask.IsCompletedSuccessfully);
      Assert.Same(first, definitionTask);
    }

    [Fact]
    public async Task DefinitionOfFieldOfSystemTypeReturnsNoLocation() {
      var source = @"
method DoIt() {
  var x := new int[0];
  var y := x.Length;
}".TrimStart();
      var documentItem = CreateTestDocument(source, "DefinitionOfFieldOfSystemTypeReturnsNoLocation.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var locations = await RequestDefinition(documentItem, (2, 14));
      Assert.False(locations.Any());
    }

    [Fact]
    public async Task DefinitionOfFunctionInvocationOfFunctionDeclaredInForeignDocumentReturnsLocation() {
      var source = @"
include ""foreign.dfy""

method DoIt() returns (x: int) {
  var a := new A();
  return a.GetX();
}".TrimStart();
      var documentItem = CreateTestDocument(source, Path.Combine(Directory.GetCurrentDirectory(), "Lookup/TestFiles/test.dfy"));
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var definition = (await RequestDefinition(documentItem, (4, 13))).Single();
      var location = definition.Location;
      Assert.Equal(DocumentUri.FromFileSystemPath(Path.Combine(Directory.GetCurrentDirectory(), "Lookup/TestFiles/foreign.dfy")), location.Uri);
      Assert.Equal(new Range((5, 11), (5, 15)), location.Range);
    }

    [Fact]
    public async Task DefinitionOfInvocationOfUnknownFunctionOrMethodReturnsNoLocation() {
      var source = @"
method DoIt() returns (x: int) {
  return GetX();
}".TrimStart();
      var documentItem = CreateTestDocument(source, "DefinitionOfInvocationOfUnknownFunctionOrMethodReturnsNoLocation.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      Assert.False((await RequestDefinition(documentItem, (1, 12))).Any());
    }

    [Fact]
    public async Task DefinitionOfVariableShadowingFieldReturnsTheVariable() {
      var source = @"
class Test {
  var x: int;

  method DoIt() {
    var x := 1;
    print x;
  }
}".TrimStart();
      var documentItem = CreateTestDocument(source, "DefinitionOfVariableShadowingFieldReturnsTheVariable.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var definition = (await RequestDefinition(documentItem, (5, 10))).Single();
      var location = definition.Location;
      Assert.Equal(documentItem.Uri, location.Uri);
      Assert.Equal(new Range((4, 8), (4, 9)), location.Range);
    }

    [Fact]
    public async Task DefinitionOfVariableShadowingFieldReturnsTheFieldIfThisIsUsed() {
      var source = @"
class Test {
  var x: int;

  method DoIt() {
    var x := 1;
    print this.x;
  }
}".TrimStart();
      var documentItem = CreateTestDocument(source, "DefinitionOfVariableShadowingFieldReturnsTheFieldIfThisIsUsed.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var definition = (await RequestDefinition(documentItem, (5, 15))).Single();
      var location = definition.Location;
      Assert.Equal(documentItem.Uri, location.Uri);
      Assert.Equal(new Range((1, 6), (1, 7)), location.Range);
    }

    [Fact]
    public async Task DefinitionOfVariableShadowingAnotherVariableReturnsTheShadowingVariable() {
      var source = @"
class Test {
  var x: int;

  method DoIt() {
    var x := 1;
    {
      var x := 2;
      print x;
    }
  }
}".TrimStart();
      var documentItem = CreateTestDocument(source, "DefinitionOfVariableShadowingAnotherVariableReturnsTheShadowingVariable.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var definition = (await RequestDefinition(documentItem, (7, 12))).Single();
      var location = definition.Location;
      Assert.Equal(documentItem.Uri, location.Uri);
      Assert.Equal(new Range((6, 10), (6, 11)), location.Range);
    }

    [Fact]
    public async Task DefinitionOfVariableShadowedByAnotherReturnsTheOriginalVariable() {
      var source = @"
class Test {
  var x: int;

  method DoIt() {
    var x := 1;
    {
      var x := 2;
    }
    print x;
  }
}".TrimStart();
      var documentItem = CreateTestDocument(source, "DefinitionOfVariableShadowedByAnotherReturnsTheOriginalVariable.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var definition = (await RequestDefinition(documentItem, (8, 10))).Single();
      var location = definition.Location;
      Assert.Equal(documentItem.Uri, location.Uri);
      Assert.Equal(new Range((4, 8), (4, 9)), location.Range);
    }

    [Fact]
    public async Task DefinitionInConstructorInvocationOfUserDefinedTypeOfForeignFileReturnsLinkToForeignFile() {
      var source = @"
include ""foreign.dfy""

method DoIt() returns (x: int) {
  var a := new A();
  return a.GetX();
}".TrimStart();
      var documentItem = CreateTestDocument(source, Path.Combine(Directory.GetCurrentDirectory(), "Lookup/TestFiles/test.dfy"));
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var aInNewA = (await RequestDefinition(documentItem, (3, 15))).Single();
      var location = aInNewA.Location;
      Assert.Equal(DocumentUri.FromFileSystemPath(Path.Combine(Directory.GetCurrentDirectory(), "Lookup/TestFiles/foreign.dfy")), location.Uri);
      Assert.Equal(new Range((3, 2), (3, 13)), location.Range);
    }

    [Fact]
    public async Task Refinement() {
      var source = @"
module {>0:A<} {
  class X { }
  class T {
    method M(x: int) returns (y: int)
      requires 0 <= x;
      ensures 0 <= y;
    {
      y := 2 * x;
    }
    method Q() returns (q: int, r: int, {>1:s<}: int)
      ensures 0 <= q && 0 <= r && 0 <= s;
    {  // error: failure to establish postcondition about q
      r, s := 100, 200;
    }
  }
}

module B refines ><A {
  class C { }
  datatype Dt = Ax | Bx
  class T ... {
    method P() returns (p: int)
    {
      p := 18;
    }
    method M(x: int) returns (y: int)
      ensures y % 2 == 0;  // add a postcondition
    method Q ...
      ensures 12 <= r;
      ensures 1200 <= ><s;  // error: postcondition is not established by
                          // inherited method body
  }
}".TrimStart();
      await AssertPositionsLineUpWithRanges(source);
    }

    public GoToDefinitionTest(ITestOutputHelper output) : base(output) {
    }
  }
}
