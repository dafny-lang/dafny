using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using OmniSharp.Extensions.LanguageServer.Protocol;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using OmniSharp.Extensions.LanguageServer.Protocol.Progress;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Lookup {
  [TestClass]
  public class DefinitionTest : ClientBasedLanguageServerTest {

    private IRequestProgressObservable<IEnumerable<LocationOrLocationLink>, LocationOrLocationLinks> RequestDefinition(TextDocumentItem documentItem, Position position) {
      return client.RequestDefinition(
        new DefinitionParams {
          TextDocument = documentItem.Uri,
          Position = position
        },
        CancellationToken
      );
    }

    [TestMethod]
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

    [TestMethod]
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
  function method PropagateFailure<U>(): Result<U, E>
    requires Err?
  {
    Err(this.er><ror)
  }
}
".TrimStart();

      await AssertPositionsLineUpWithRanges(source);
    }

    private async Task AssertPositionsLineUpWithRanges(string source) {
      MarkupTestFile.GetPositionsAndNamedRanges(source, out var cleanSource,
        out var positions, out var ranges);

      var documentItem = CreateTestDocument(cleanSource);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      for (var index = 0; index < positions.Count; index++) {
        var position = positions[index];
        var range = ranges.ContainsKey(string.Empty) ? ranges[string.Empty][index] : ranges[index.ToString()].Single();
        var result = (await RequestDefinition(documentItem, position).AsTask()).Single();
        Assert.AreEqual(range, result.Location!.Range);
      }
    }

    [TestMethod]
    public async Task StaticFunctionCall() {
      var source = @"
module [>Zaz<] {
  trait [>E<] {
    static function method [>Foo<](): E
  }
}

function Bar(): Zaz.E {
  Z><az.><E.F><oo()
}
".TrimStart();

      await AssertPositionsLineUpWithRanges(source);
    }

    [TestMethod]
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
      var documentItem = CreateTestDocument(cleanSource);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);

      var fibonacciSpecOnItself = (await RequestDefinition(documentItem, positions[0]).AsTask());
      Assert.IsFalse(fibonacciSpecOnItself.Any());

      var nOnItself = (await RequestDefinition(documentItem, positions[1]).AsTask());
      Assert.IsFalse(nOnItself.Any());

      var fibonacciCall = (await RequestDefinition(documentItem, positions[2]).AsTask()).Single();
      Assert.AreEqual(ranges[0], fibonacciCall.Location!.Range);

      var typeParameter = (await RequestDefinition(documentItem, positions[3]).AsTask()).Single();
      Assert.AreEqual(ranges[1], typeParameter.Location!.Range);
    }

    [TestMethod]
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
      var documentItem = CreateTestDocument(cleanSource);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var matchSource = (await RequestDefinition(documentItem, positions[0]).AsTask()).Single();
      Assert.AreEqual(ranges[2], matchSource.Location!.Range);

      // TODO doesn't work right now because we use post match compilation information.
      // var identity = (await RequestDefinition(documentItem, positions[1]).AsTask()).Single();
      // Assert.AreEqual(ranges[0], identity.Location!.Range);

      // TODO doesn't work right now because we use post match compilation information.
      // var green = (await RequestDefinition(documentItem, positions[2]).AsTask()).Single();
      // Assert.AreEqual(ranges[1], green.Location!.Range);

      var matchSourceStmt = (await RequestDefinition(documentItem, positions[3]).AsTask()).Single();
      Assert.AreEqual(ranges[3], matchSourceStmt.Location!.Range);

      // TODO doesn't work right now because we use post match compilation information.
      // var identityStmt = (await RequestDefinition(documentItem, positions[4]).AsTask()).Single();
      // Assert.AreEqual(ranges[0], identity.Location!.Range);

      // TODO doesn't work right now because we use post match compilation information.
      // var greenStmt = (await RequestDefinition(documentItem, positions[5]).AsTask()).Single();
      // Assert.AreEqual(ranges[1], green.Location!.Range);
    }

    [TestMethod]
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
      var documentItem = CreateTestDocument(cleanSource);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var usizeReference = (await RequestDefinition(documentItem, positions[2]).AsTask()).Single();
      Assert.AreEqual(documentItem.Uri, usizeReference.Location!.Uri);
      Assert.AreEqual(ranges[1], usizeReference.Location.Range);

      var lengthDefinition = (await RequestDefinition(documentItem, positions[1]).AsTask());
      Assert.IsFalse(lengthDefinition.Any());

      var providerImport = (await RequestDefinition(documentItem, positions[0]).AsTask()).Single();
      Assert.AreEqual(ranges[0], providerImport.Location!.Range);

      var lengthAssignment = (await RequestDefinition(documentItem, positions[3]).AsTask()).Single();
      Assert.AreEqual(ranges[2], lengthAssignment.Location!.Range);
    }

    [TestMethod]
    public async Task JumpToOtherModule() {
      var source = @"
module Provider {
  class A {
    var [>x<]: int;

    constructor() {}

    function method [>GetX<](): int
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
  import [>Provider<]

  type A2 = Pro><vider.A
}".TrimStart();

      await AssertPositionsLineUpWithRanges(source);
    }

    [TestMethod]
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
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);

      var containerReference = (await RequestDefinition(documentItem, (9, 11)).AsTask()).Single();
      Assert.AreEqual(new Range((0, 7), (0, 16)), containerReference.Location!.Range);

      var getItCall = (await RequestDefinition(documentItem, (9, 23)).AsTask()).Single();
      Assert.AreEqual(new Range((1, 9), (1, 14)), getItCall.Location!.Range);

      var doItCall = (await RequestDefinition(documentItem, (10, 12)).AsTask()).Single();
      Assert.AreEqual(new Range((4, 9), (4, 13)), doItCall.Location!.Range);

      var xVar = (await RequestDefinition(documentItem, (10, 17)).AsTask()).Single();
      Assert.AreEqual(new Range((9, 6), (9, 7)), xVar.Location!.Range);
    }

    [TestMethod]
    public async Task DefinitionReturnsBeforeVerificationIsComplete() {
      var documentItem = CreateTestDocument(NeverVerifies);
      client.OpenDocument(documentItem);
      var verificationTask = GetLastDiagnostics(documentItem, CancellationToken);
      var definitionTask = RequestDefinition(documentItem, (4, 14)).AsTask();
      var first = await Task.WhenAny(verificationTask, definitionTask);
      Assert.IsFalse(verificationTask.IsCompleted);
      Assert.AreSame(first, definitionTask);
    }

    [TestMethod]
    public async Task DefinitionOfFieldOfSystemTypeReturnsNoLocation() {
      var source = @"
method DoIt() {
  var x := new int[0];
  var y := x.Length;
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      Assert.IsFalse((await RequestDefinition(documentItem, (2, 14)).AsTask()).Any());
    }

    [TestMethod]
    public async Task DefinitionOfFunctionInvocationOfFunctionDeclaredInForeignDocumentReturnsLocation() {
      var source = @"
include ""foreign.dfy""

method DoIt() returns (x: int) {
  var a := new A();
  return a.GetX();
}".TrimStart();
      var documentItem = CreateTestDocument(source, Path.Combine(Directory.GetCurrentDirectory(), "Lookup/TestFiles/test.dfy"));
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var definition = (await RequestDefinition(documentItem, (4, 13)).AsTask()).Single();
      var location = definition.Location;
      Assert.AreEqual(DocumentUri.FromFileSystemPath(Path.Combine(Directory.GetCurrentDirectory(), "Lookup/TestFiles/foreign.dfy")), location.Uri);
      Assert.AreEqual(new Range((5, 18), (5, 22)), location.Range);
    }

    [TestMethod]
    public async Task DefinitionOfInvocationOfUnknownFunctionOrMethodReturnsNoLocation() {
      var source = @"
method DoIt() returns (x: int) {
  return GetX();
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      Assert.IsFalse((await RequestDefinition(documentItem, (1, 12)).AsTask()).Any());
    }

    [TestMethod]
    public async Task DefinitionOfVariableShadowingFieldReturnsTheVariable() {
      var source = @"
class Test {
  var x: int;

  method DoIt() {
    var x := 1;
    print x;
  }
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var definition = (await RequestDefinition(documentItem, (5, 10)).AsTask()).Single();
      var location = definition.Location;
      Assert.AreEqual(documentItem.Uri, location.Uri);
      Assert.AreEqual(new Range((4, 8), (4, 9)), location.Range);
    }

    [TestMethod]
    public async Task DefinitionOfVariableShadowingFieldReturnsTheFieldIfThisIsUsed() {
      var source = @"
class Test {
  var x: int;

  method DoIt() {
    var x := 1;
    print this.x;
  }
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var definition = (await RequestDefinition(documentItem, (5, 15)).AsTask()).Single();
      var location = definition.Location;
      Assert.AreEqual(documentItem.Uri, location.Uri);
      Assert.AreEqual(new Range((1, 6), (1, 7)), location.Range);
    }

    [TestMethod]
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
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var definition = (await RequestDefinition(documentItem, (7, 12)).AsTask()).Single();
      var location = definition.Location;
      Assert.AreEqual(documentItem.Uri, location.Uri);
      Assert.AreEqual(new Range((6, 10), (6, 11)), location.Range);
    }

    [TestMethod]
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
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var definition = (await RequestDefinition(documentItem, (8, 10)).AsTask()).Single();
      var location = definition.Location;
      Assert.AreEqual(documentItem.Uri, location.Uri);
      Assert.AreEqual(new Range((4, 8), (4, 9)), location.Range);
    }

    [TestMethod]
    public async Task DefinitionInConstructorInvocationOfUserDefinedTypeOfForeignFileReturnsLinkToForeignFile() {
      var source = @"
include ""foreign.dfy""

method DoIt() returns (x: int) {
  var a := new A();
  return a.GetX();
}".TrimStart();
      var documentItem = CreateTestDocument(source, Path.Combine(Directory.GetCurrentDirectory(), "Lookup/TestFiles/test.dfy"));
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var aInNewA = (await RequestDefinition(documentItem, (3, 15)).AsTask()).Single();
      var location = aInNewA.Location;
      Assert.AreEqual(DocumentUri.FromFileSystemPath(Path.Combine(Directory.GetCurrentDirectory(), "Lookup/TestFiles/foreign.dfy")), location.Uri);
      Assert.AreEqual(new Range((3, 2), (3, 13)), location.Range);
    }
  }
}
