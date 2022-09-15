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
  while(true) {
    if (x > 2) {
      break;
    }
    x := x + 1;
  }
}
".TrimStart();

      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var whileReference = (await RequestDefinition(documentItem, (4, 8)).AsTask()).Single();
      Assert.AreEqual(new Range((2, 2), (2, 7)), whileReference.Location!.Range);
    }

    [TestMethod]
    public async Task MatchExprAndMethodWithoutBody() {
      var source = @"  
datatype Option<+U> = None | Some(val: U) {

  function FMap<V>(f: U -> V): Option<V> {
    match this
    case None => None
    case Some(x) => Some(f(x))
  }
}

datatype A = A {
  static method create() returns (ret: A)
}
datatype Result<T, E> = Ok(value: T) | Err(error: E) {
  function method PropagateFailure<U>(): Result<U, E>
    requires Err?
  {
    Err(this.error)
  }
}
".TrimStart();

      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var noneCreation = (await RequestDefinition(documentItem, (4, 19)).AsTask()).Single();
      Assert.AreEqual(new Range((0, 22), (0, 26)), noneCreation.Location.Range);

      var errorInThisDotError = (await RequestDefinition(documentItem, (16, 15)).AsTask()).Single();
      Assert.AreEqual(new Range((12, 43), (12, 48)), errorInThisDotError.Location.Range);
    }

    [TestMethod]
    public async Task StaticFunctionCall() {
      var source = @"
module Zaz {
  trait E {
    static function method Foo(): E
  }
}

function Bar(): Zaz.E {
  Zaz.E.Foo()
}
".TrimStart();

      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var zazReference = (await RequestDefinition(documentItem, (7, 2)).AsTask()).Single();
      Assert.AreEqual(new Range((0, 7), (0, 10)), zazReference.Location!.Range);

      var eReference = (await RequestDefinition(documentItem, (7, 6)).AsTask()).Single();
      Assert.AreEqual(new Range((1, 8), (1, 9)), eReference.Location!.Range);

      var fooReference = (await RequestDefinition(documentItem, (7, 8)).AsTask()).Single();
      Assert.AreEqual(new Range((2, 27), (2, 30)), fooReference.Location!.Range);
    }

    [TestMethod]
    public async Task FunctionCallAndGotoOnDeclaration() {
      var source = @"
function FibonacciSpec(n: nat): nat {
  if (n == 0) then 0
  else if (n == 1) then 1
  else FibonacciSpec(n - 1) + FibonacciSpec(n - 2)
}

type seq31<T> = x: seq<T> | 0 <= |x| <= 32 as int
".TrimStart();

      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var definition = (await RequestDefinition(documentItem, (3, 8)).AsTask()).Single();
      var location = definition.Location;
      Assert.AreEqual(documentItem.Uri, location.Uri);
      Assert.AreEqual(new Range((0, 9), (0, 22)), location.Range);

      var fibonacciSpecOnItself = (await RequestDefinition(documentItem, (0, 12)).AsTask());
      Assert.IsFalse(fibonacciSpecOnItself.Any());

      var nOnItself = (await RequestDefinition(documentItem, (0, 23)).AsTask());
      Assert.IsFalse(nOnItself.Any());

      var typeParameter = (await RequestDefinition(documentItem, (6, 23)).AsTask()).Single();
      Assert.AreEqual(new Range((6, 11), (6, 12)), typeParameter.Location!.Range);
    }

    [TestMethod]
    public async Task DatatypesAndMatches() {
      var source = @"
datatype Identity<T> = Identity(value: T)
datatype Colors = Red | Green | Blue

function Foo(value: Identity<Colors>): bool {
  match value {
    case Identity(Red()) => true
    case Identity(Green) => false // Warning
    case Identity(Blue()) => false
  }
}

method Bar(value: Identity<Colors>) returns (x: bool) {
  match value {
    case Identity(Red()) => return true;
    case Identity(Green) => return false; // Warning
    case Identity(Blue()) => return false;
  }
}
".TrimStart();

      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var matchSource = (await RequestDefinition(documentItem, (4, 10)).AsTask()).Single();
      Assert.AreEqual(new Range((3, 13), (3, 18)), matchSource.Location!.Range);

      // TODO doesn't work right now because we use post match compilation information.
      // var identity = (await RequestDefinition(documentItem, (5, 12)).AsTask()).Single();
      // Assert.AreEqual(new Range((0, 23), (0, 31)), identity.Location!.Range);

      // TODO doesn't work right now because we use post match compilation information.
      // var green = (await RequestDefinition(documentItem, (6, 20)).AsTask()).Single();
      // Assert.AreEqual(new Range((1, 24), (1, 29)), green.Location!.Range);

      var matchSourceStmt = (await RequestDefinition(documentItem, (12, 10)).AsTask()).Single();
      Assert.AreEqual(new Range((11, 11), (11, 16)), matchSourceStmt.Location!.Range);

      // TODO doesn't work right now because we use post match compilation information.
      // var identityStmt = (await RequestDefinition(documentItem, (13, 12)).AsTask()).Single();
      // Assert.AreEqual(new Range((0, 23), (0, 31)), identity.Location!.Range);

      // TODO doesn't work right now because we use post match compilation information.
      // var greenStmt = (await RequestDefinition(documentItem, (14, 20)).AsTask()).Single();
      // Assert.AreEqual(new Range((1, 24), (1, 29)), green.Location!.Range);
    }

    [TestMethod]
    public async Task JumpToExternModule() {
      var source = @"
module {:extern} Provider {
  newtype nat64 = x: int | 0 <= x <= 0xffff_ffff_ffff_ffff
  type usize = nat64
}

module Consumer {
  import opened Provider

  method DoIt() {
    var length: usize := 3;
    length := 4;
  }
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var usizeReference = (await RequestDefinition(documentItem, (9, 19)).AsTask()).Single();
      Assert.AreEqual(documentItem.Uri, usizeReference.Location.Uri);
      Assert.AreEqual(new Range((2, 7), (2, 12)), usizeReference.Location.Range);

      var lengthDefinition = (await RequestDefinition(documentItem, (9, 10)).AsTask());
      Assert.IsFalse(lengthDefinition.Any());

      var providerImport = (await RequestDefinition(documentItem, (6, 16)).AsTask()).Single();
      Assert.AreEqual(new Range((0, 17), (0, 25)), providerImport.Location!.Range);

      var lengthAssignment = (await RequestDefinition(documentItem, (10, 7)).AsTask()).Single();
      Assert.AreEqual(new Range((9, 8), (9, 14)), lengthAssignment.Location!.Range);
    }

    [TestMethod]
    public async Task JumpToOtherModule() {
      var source = @"
module Provider {
  class A {
    var x: int;

    constructor() {}

    function method GetX(): int
      reads this`x
    {
      this.x
    }
  }
}

module Consumer {
  import opened Provider

  method DoIt() returns (x: int) {
    var a := new A();
    return a.GetX();
  }
}

module Consumer2 {
  import Provider

  type A2 = Provider.A
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var getXCall = (await RequestDefinition(documentItem, (19, 13)).AsTask()).Single();
      Assert.AreEqual(new Range((6, 20), (6, 24)), getXCall.Location!.Range);

      var xInFrame = (await RequestDefinition(documentItem, (7, 17)).AsTask()).Single();
      Assert.AreEqual(new Range((2, 8), (2, 9)), xInFrame.Location!.Range);

      var providerQualifier = (await RequestDefinition(documentItem, (26, 14)).AsTask()).Single();
      Assert.AreEqual(new Range((24, 9), (24, 17)), providerQualifier.Location!.Range);
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