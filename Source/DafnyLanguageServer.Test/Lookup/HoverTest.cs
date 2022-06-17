using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using OmniSharp.Extensions.LanguageServer.Protocol.Client;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.IO;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Lookup {
  [TestClass]
  public class HoverTest : ClientBasedLanguageServerTest {

    [TestInitialize]
    public override async Task SetUp() {
      DafnyOptions.Install(DafnyOptions.Create("-proverOpt:SOLVER=noop"));
      await base.SetUp();
    }

    private Task<Hover> RequestHover(TextDocumentItem documentItem, Position position) {
      return client.RequestHover(
        new HoverParams {
          TextDocument = documentItem.Uri,
          Position = position
        },
        CancellationToken
      );
    }

    private async Task AssertHoverContains(TextDocumentItem documentItem, Position position, string expectedContent) {
      var hover = await RequestHover(documentItem, position);
      Assert.IsNotNull(hover);
      var markup = hover.Contents.MarkupContent;
      Assert.IsNotNull(markup);
      Assert.AreEqual(MarkupKind.Markdown, markup.Kind);
      Assert.IsTrue(markup.Value.Contains(expectedContent), "Could not find {1} in {0}", markup.Value, expectedContent);
    }

    [TestMethod]
    public async Task HoveringMethodInvocationOfMethodDeclaredInSameDocumentReturnsSignature() {
      var source = @"
method DoIt() returns (x: int) {
}

method CallDoIt() returns () {
  var x := DoIt();
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await AssertHoverContains(documentItem, (4, 14), "```dafny\nmethod DoIt() returns (x: int)\n```");
    }

    [TestMethod]
    public async Task HoverReturnsBeforeVerificationIsComplete() {
      var documentItem = CreateTestDocument(NeverVerifies);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);

      var verificationTask = GetLastDiagnostics(documentItem, CancellationToken);
      var definitionTask = RequestHover(documentItem, (4, 14));
      var first = await Task.WhenAny(verificationTask, definitionTask);
      Assert.IsFalse(verificationTask.IsCompleted);
      Assert.AreSame(first, definitionTask, first.ToString());
    }

    [TestMethod]
    public async Task AssHoveringFieldOfSystemTypeReturnsDefinition() {
      var source = @"
method DoIt() {
  var x := new int[0];
  var y := x.Length;
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await AssertHoverContains(documentItem, (2, 14), "```dafny\nconst array.Length: int\n```");
    }

    [TestMethod]
    public async Task HoveringFunctionInvocationOfFunctionDeclaredInForeignDocumentReturnsSignature() {
      // TODO Actually, the invoked function is a compiled function.
      var source = @"
include ""foreign.dfy""

method DoIt() returns (x: int) {
  var a := new A();
  return a.GetX();
}".TrimStart();
      var documentItem = CreateTestDocument(source, Path.Combine(Directory.GetCurrentDirectory(), "Lookup/TestFiles/test.dfy"));
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await AssertHoverContains(documentItem, (4, 13), "```dafny\nfunction A.GetX(): int\n```");
    }

    [TestMethod]
    public async Task HoveringInvocationOfUnknownFunctionOrMethodReturnsNull() {
      var source = @"
method DoIt() returns (x: int) {
  return GetX();
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var hover = await RequestHover(documentItem, (1, 12));
      Assert.IsNull(hover);
    }

    [TestMethod]
    public async Task HoveringVariableShadowingFieldReturnsTheVariable() {
      var source = @"
class Test {
  var x: int;

  method DoIt() {
    var x := """";
    print x;
  }
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await AssertHoverContains(documentItem, (5, 10), "```dafny\nx: string\n```");
    }

    [TestMethod]
    public async Task HoveringVariableShadowingFieldReturnsTheFieldIfThisIsUsed() {
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
      await AssertHoverContains(documentItem, (5, 15), "```dafny\nvar Test.x: int\n```");
    }

    [TestMethod]
    public async Task HoveringVariableShadowingAnotherVariableReturnsTheShadowingVariable() {
      var source = @"
class Test {
  var x: int;

  method DoIt() {
    var x := 1;
    {
      var x := ""2"";
      print x;
    }
  }
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await AssertHoverContains(documentItem, (7, 12), "```dafny\nx: string\n```");
    }

    [TestMethod]
    public async Task HoveringVariableShadowedByAnotherReturnsTheOriginalVariable() {
      var source = @"
class Test {
  var x: int;

  method DoIt() {
    var x := ""1"";
    {
      var x := 2;
    }
    print x;
  }
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await AssertHoverContains(documentItem, (8, 10), "```dafny\nx: string\n```");
    }

    [TestMethod]
    public async Task HoveringTypeOfFieldReturnsTheUserDefinedType() {
      var source = @"
class A {
  constructor() {}
}

class B {
  var a: A;

  constructor() {
    a := new A();
  }
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await AssertHoverContains(documentItem, (5, 9), "```dafny\nclass A\n```");
    }

    [TestMethod]
    public async Task HoveringTypeOfConstructorInvocationReturnsTheUserDefinedType() {
      var source = @"
class A {
  constructor() {}
}

class B {
  var a: A;

  constructor() {
    a := new A();
  }
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await AssertHoverContains(documentItem, (8, 13), "```dafny\nclass A\n```");
    }

    [TestMethod]
    public async Task HoveringParameterOfMethodReturnsTheUserDefinedType() {
      var source = @"
class A {
  constructor() {}
}

method DoIt(a: A) {}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await AssertHoverContains(documentItem, (4, 15), "```dafny\nclass A\n```");
    }

    [TestMethod]
    public async Task HoveringParentTraitOfUserDefinedTypeReturnsTheParentTrait() {
      var source = @"
trait Base {}
class Sub extends Base {}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await AssertHoverContains(documentItem, (1, 19), "```dafny\ntrait Base\n```");
    }

    [TestMethod]
    public async Task HoveringParameterDesignatorOfMethodInsideDataTypeReturnsTheParameterType() {
      var source = @"
datatype SomeType = SomeType {
  method AssertEqual(x: int, y: int) {
    var j:=x == y;
  }
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      client.OpenDocument(documentItem);
      await AssertHoverContains(documentItem, (2, 11), "```dafny\nx: int\n```");
    }

    [TestMethod]
    public async Task HoveringMethodInvocationOfDataTypeReturnsMethodSignature() {
      var source = @"
datatype SomeType = SomeType {
  method AssertEqual(x: int, y: int) {
    assert x == y;
  }
}

method Main() {
  var instance: SomeType;
  instance.AssertEqual(1, 2);
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      client.OpenDocument(documentItem);
      await AssertHoverContains(documentItem, (8, 12), "```dafny\nmethod SomeType.AssertEqual(x: int, y: int)\n```");
    }

    [TestMethod]
    public async Task HoveringFormalReturnsFormalType() {
      var source = @"
method f(i: int) {
  var r := i;
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await AssertHoverContains(documentItem, (0, 9), "```dafny\ni: int\n```");
    }

    [TestMethod]
    public async Task HoveringDeclarationVariableReturnsInferredVariableType() {
      var source = @"
method f(i: int) {
  var r := i;
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await AssertHoverContains(documentItem, (1, 6), "```dafny\nr: int\n```");
    }

    [TestMethod]
    public async Task HoveringForallBoundVarReturnsBoundVarInferredType() {
      var source = @"
method f(i: int) {
  var x:=forall j :: j + i == i + j;
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await AssertHoverContains(documentItem, (1, 17), "```dafny\nj: int\n```");
      await AssertHoverContains(documentItem, (1, 22), "```dafny\nj: int\n```");
    }

    [TestMethod]
    public async Task HoveringExistsBoundVarReturnsBoundVarInferredType() {
      var source = @"
method f(i: int) {
  var x:=exists j :: j + i == i;
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await AssertHoverContains(documentItem, (1, 17), "```dafny\nj: int\n```");
      await AssertHoverContains(documentItem, (1, 22), "```dafny\nj: int\n```");
    }

    [TestMethod]
    public async Task HoveringSetBoundVarReturnsBoundVarInferredType() {
      var source = @"
method f(i: int) {
  var x := {1, 2, 3};
  var y := set j | j in x && j < 3;
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await AssertHoverContains(documentItem, (2, 16), "```dafny\nj: int\n```");
      await AssertHoverContains(documentItem, (2, 20), "```dafny\nj: int\n```");
    }

    [TestMethod]
    public async Task HoveringMapBoundVarReturnsBoundVarInferredType() {
      var source = @"
method f(i: int) {
  var m := map j : int | 0 <= j <= i :: j * j;
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await AssertHoverContains(documentItem, (1, 16), "```dafny\nj: int\n```");
      await AssertHoverContains(documentItem, (1, 31), "```dafny\nj: int\n```");
    }

    [TestMethod]
    public async Task HoveringLambdaBoundVarReturnsBoundVarInferredType() {
      var source = @"
method f(i: int) {
  var m := j => j * i;
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await AssertHoverContains(documentItem, (1, 12), "```dafny\nj: int\n```");
      await AssertHoverContains(documentItem, (1, 17), "```dafny\nj: int\n```");
    }

    [TestMethod]
    public async Task HoveringForAllBoundVarInPredicateReturnsBoundVarInferredType() {
      var source = @"
predicate f(i: int) {
  forall j :: j + i == i + j
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await AssertHoverContains(documentItem, (1, 10), "```dafny\nj: int\n```");
      await AssertHoverContains(documentItem, (1, 15), "```dafny\nj: int\n```");
    }

    [TestMethod]
    public async Task HoveringByMethodReturnsInferredType() {
      var source = @"
predicate even(n: nat)
  ensures even(n) <==> n % 2 == 0 
{
  if n < 2 then n == 0 else even(n - 2)
} by method {
  var x := n % 2 == 0;
  return x;
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await AssertHoverContains(documentItem, (5, 7), "```dafny\nx: bool\n```");
      await AssertHoverContains(documentItem, (5, 12), "```dafny\nn: nat\n```");
    }

    [TestMethod]
    public async Task HoveringLetInReturnsInferredType() {
      var source = @"
function method test(n: nat): nat {
  var i := n * 2;
  if i == 4 then 3 else 2
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await AssertHoverContains(documentItem, (1, 7), "```dafny\ni: int\n```");
      await AssertHoverContains(documentItem, (1, 12), "```dafny\nn: nat\n```");
    }

    [TestMethod]
    public async Task HoveringSpecificationBoundVariableReturnsInferredType() {
      var source = @"
method returnBiggerThan(n: nat) returns (y: int)
  requires var y := 100; forall i :: i < n ==> i < y 
  ensures forall i :: i > y ==> i > n 
 {
  return n + 2;
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await AssertHoverContains(documentItem, (1, 16), "```dafny\ny: int\n```");
      await AssertHoverContains(documentItem, (1, 33), "```dafny\ni: int\n```");
    }

    [TestMethod]
    public async Task HoveringResultVarReturnsInferredType() {
      var source = @"
function f(i: int): (r: int)
  ensures r - i < 10
{
  i + 2
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await AssertHoverContains(documentItem, (0, 22), "```dafny\nr: int\n```");
      await AssertHoverContains(documentItem, (1, 11), "```dafny\nr: int\n```");
    }

    [TestMethod]
    public async Task HoverIngInferredVariable() {
      var source = @"
datatype Pos = Pos(line: int)
function method f(i: int): Pos {
  if i <= 3 then Pos(i)
  else
   var r := f(i - 2);
   Pos(r.line + 2)
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await AssertHoverContains(documentItem, (4, 8), "```dafny\nr: Pos\n```");
    }

    [TestMethod]
    public async Task HoverIngResultTypeShouldNotCrash() {
      var source = @"
datatype Position = Position(Line: nat)
function ToRelativeIndependent(): (p: Position)
{
   Position(12)
}
".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      await AssertHoverContains(documentItem, (1, 41), "```dafny\ndatatype Position\n```");
    }
  }
}
