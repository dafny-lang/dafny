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

    private Task<Hover> RequestHover(TextDocumentItem documentItem, Position position) {
      return client.RequestHover(
        new HoverParams {
          TextDocument = documentItem.Uri,
          Position = position
        },
        CancellationToken
      );
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
      var hover = await RequestHover(documentItem, (4, 14));
      Assert.IsNotNull(hover);
      var markup = hover.Contents.MarkupContent;
      Assert.AreEqual(MarkupKind.Markdown, markup.Kind);
      Assert.AreEqual("```dafny\nmethod DoIt() returns (x: int)\n```", markup.Value);
    }

    [TestMethod]
    public async Task HoverReturnsBeforeVerificationIsComplete() {
      var documentItem = CreateTestDocument(NeverVerifies);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);

      client.OpenDocument(documentItem);
      var verificationTask = diagnosticReceiver.AwaitVerificationDiagnosticsAsync(CancellationToken);
      var definitionTask = RequestHover(documentItem, (4, 14));
      var first = await Task.WhenAny(verificationTask, definitionTask);
      Assert.AreSame(first, definitionTask);
    }

    [TestMethod]
    public async Task HoveringFieldOfSystemTypeReturnsDefinition() {
      var source = @"
method DoIt() {
  var x := new int[0];
  var y := x.Length;
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var hover = await RequestHover(documentItem, (2, 14));
      Assert.IsNotNull(hover);
      var markup = hover.Contents.MarkupContent;
      Assert.AreEqual(MarkupKind.Markdown, markup.Kind);
      Assert.AreEqual("```dafny\nconst array.Length: int\n```", markup.Value);
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
      var hover = await RequestHover(documentItem, (4, 13));
      Assert.IsNotNull(hover);
      var markup = hover.Contents.MarkupContent;
      Assert.AreEqual(MarkupKind.Markdown, markup.Kind);
      Assert.AreEqual("```dafny\nfunction A.GetX(): int\n```", markup.Value);
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
      var hover = await RequestHover(documentItem, (5, 10));
      Assert.IsNotNull(hover);
      var markup = hover.Contents.MarkupContent;
      Assert.AreEqual(MarkupKind.Markdown, markup.Kind);
      Assert.AreEqual("```dafny\nx: string\n```", markup.Value);
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
      var hover = await RequestHover(documentItem, (5, 15));
      Assert.IsNotNull(hover);
      var markup = hover.Contents.MarkupContent;
      Assert.AreEqual(MarkupKind.Markdown, markup.Kind);
      Assert.AreEqual("```dafny\nvar Test.x: int\n```", markup.Value);
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
      var hover = await RequestHover(documentItem, (7, 12));
      Assert.IsNotNull(hover);
      var markup = hover.Contents.MarkupContent;
      Assert.AreEqual(MarkupKind.Markdown, markup.Kind);
      Assert.AreEqual("```dafny\nx: string\n```", markup.Value);
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
      var hover = await RequestHover(documentItem, (8, 10));
      Assert.IsNotNull(hover);
      var markup = hover.Contents.MarkupContent;
      Assert.AreEqual(MarkupKind.Markdown, markup.Kind);
      Assert.AreEqual("```dafny\nx: string\n```", markup.Value);
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
      var hover = await RequestHover(documentItem, (5, 9));
      Assert.IsNotNull(hover);
      var markup = hover.Contents.MarkupContent;
      Assert.AreEqual(MarkupKind.Markdown, markup.Kind);
      Assert.AreEqual("```dafny\nclass A\n```", markup.Value);
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
      var hover = await RequestHover(documentItem, (8, 13));
      Assert.IsNotNull(hover);
      var markup = hover.Contents.MarkupContent;
      Assert.AreEqual(MarkupKind.Markdown, markup.Kind);
      Assert.AreEqual("```dafny\nclass A\n```", markup.Value);
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
      var hover = await RequestHover(documentItem, (4, 15));
      Assert.IsNotNull(hover);
      var markup = hover.Contents.MarkupContent;
      Assert.AreEqual(MarkupKind.Markdown, markup.Kind);
      Assert.AreEqual("```dafny\nclass A\n```", markup.Value);
    }

    [TestMethod]
    public async Task HoveringParentTraitOfUserDefinedTypeReturnsTheParentTrait() {
      var source = @"
trait Base {}
class Sub extends Base {}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var hover = await RequestHover(documentItem, (1, 19));
      Assert.IsNotNull(hover);
      var markup = hover.Contents.MarkupContent;
      Assert.AreEqual(MarkupKind.Markdown, markup.Kind);
      Assert.AreEqual("```dafny\ntrait Base\n```", markup.Value);
    }

    [TestMethod]
    public async Task HoveringParameterDesignatorOfMethodInsideDataTypeReturnsTheParameterType() {
      var source = @"
datatype SomeType = SomeType {
  method AssertEqual(x: int, y: int) {
    assert x == y;
  }
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      client.OpenDocument(documentItem);
      var hover = await RequestHover(documentItem, (2, 11));
      Assert.IsNotNull(hover);
      var markup = hover.Contents.MarkupContent;
      Assert.AreEqual(MarkupKind.Markdown, markup.Kind);
      Assert.AreEqual("```dafny\nx: int\n```", markup.Value);
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
      var hover = await RequestHover(documentItem, (8, 12));
      Assert.IsNotNull(hover);
      var markup = hover.Contents.MarkupContent;
      Assert.AreEqual(MarkupKind.Markdown, markup.Kind);
      Assert.AreEqual("```dafny\nmethod SomeType.AssertEqual(x: int, y: int)\n```", markup.Value);
    }

    [TestMethod]
    public async Task HoveringFormalReturnsFormalType() {
      var source = @"
method f(i: int) {
  var r := i;
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var hover = await RequestHover(documentItem, (0, 9));
      Assert.IsNotNull(hover);
      var markup = hover.Contents.MarkupContent;
      Assert.AreEqual(MarkupKind.Markdown, markup.Kind);
      Assert.AreEqual("```dafny\ni: int\n```", markup.Value);
    }

    [TestMethod]
    public async Task HoveringDeclarationVariableReturnsInferredVariableType() {
      var source = @"
method f(i: int) {
  var r := i;
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var hover = await RequestHover(documentItem, (1, 6));
      Assert.IsNotNull(hover);
      var markup = hover.Contents.MarkupContent;
      Assert.AreEqual(MarkupKind.Markdown, markup.Kind);
      Assert.AreEqual("```dafny\nr: int\n```", markup.Value);
    }

    [TestMethod]
    public async Task HoveringForallBoundVarReturnsBoundVarInferredType() {
      var source = @"
method f(i: int) {
  assert forall j :: j + i == i + j;
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var hover = await RequestHover(documentItem, (1, 17));
      Assert.IsNotNull(hover);
      var markup = hover.Contents.MarkupContent;
      Assert.AreEqual(MarkupKind.Markdown, markup.Kind);
      Assert.AreEqual("```dafny\nj: int\n```", markup.Value);
      hover = await RequestHover(documentItem, (1, 22));
      Assert.IsNotNull(hover);
      markup = hover.Contents.MarkupContent;
      Assert.AreEqual(MarkupKind.Markdown, markup.Kind);
      Assert.AreEqual("```dafny\nj: int\n```", markup.Value);
    }

    [TestMethod]
    public async Task HoveringExistsBoundVarReturnsBoundVarInferredType() {
      var source = @"
method f(i: int) {
  assert exists j :: j + i == i;
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var hover = await RequestHover(documentItem, (1, 17));
      Assert.IsNotNull(hover);
      var markup = hover.Contents.MarkupContent;
      Assert.AreEqual(MarkupKind.Markdown, markup.Kind);
      Assert.AreEqual("```dafny\nj: int\n```", markup.Value);
      hover = await RequestHover(documentItem, (1, 22));
      Assert.IsNotNull(hover);
      markup = hover.Contents.MarkupContent;
      Assert.AreEqual(MarkupKind.Markdown, markup.Kind);
      Assert.AreEqual("```dafny\nj: int\n```", markup.Value);
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
      var hover = await RequestHover(documentItem, (2, 16));
      Assert.IsNotNull(hover);
      var markup = hover.Contents.MarkupContent;
      Assert.AreEqual(MarkupKind.Markdown, markup.Kind);
      Assert.AreEqual("```dafny\nj: int\n```", markup.Value);
      hover = await RequestHover(documentItem, (2, 20));
      Assert.IsNotNull(hover);
      markup = hover.Contents.MarkupContent;
      Assert.AreEqual(MarkupKind.Markdown, markup.Kind);
      Assert.AreEqual("```dafny\nj: int\n```", markup.Value);
    }

    [TestMethod]
    public async Task HoveringMapBoundVarReturnsBoundVarInferredType() {
      var source = @"
method f(i: int) {
  var m := map j : int | 0 <= j <= i :: j * j;
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var hover = await RequestHover(documentItem, (1, 16));
      Assert.IsNotNull(hover);
      var markup = hover.Contents.MarkupContent;
      Assert.AreEqual(MarkupKind.Markdown, markup.Kind);
      Assert.AreEqual("```dafny\nj: int\n```", markup.Value);
      hover = await RequestHover(documentItem, (1, 31));
      Assert.IsNotNull(hover);
      markup = hover.Contents.MarkupContent;
      Assert.AreEqual(MarkupKind.Markdown, markup.Kind);
      Assert.AreEqual("```dafny\nj: int\n```", markup.Value);
    }

    [TestMethod]
    public async Task HoveringLambdaBoundVarReturnsBoundVarInferredType() {
      var source = @"
method f(i: int) {
  var m := j => j * i;
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var hover = await RequestHover(documentItem, (1, 12));
      Assert.IsNotNull(hover);
      var markup = hover.Contents.MarkupContent;
      Assert.AreEqual(MarkupKind.Markdown, markup.Kind);
      Assert.AreEqual("```dafny\nj: int\n```", markup.Value);
      hover = await RequestHover(documentItem, (1, 17));
      Assert.IsNotNull(hover);
      markup = hover.Contents.MarkupContent;
      Assert.AreEqual(MarkupKind.Markdown, markup.Kind);
      Assert.AreEqual("```dafny\nj: int\n```", markup.Value);
    }

    [TestMethod]
    public async Task HoveringForAllBoundVarInPredicateReturnsBoundVarInferredType() {
      var source = @"
predicate f(i: int) {
  forall j :: j + i == i + j
}".TrimStart();
      var documentItem = CreateTestDocument(source);
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);
      var hover = await RequestHover(documentItem, (1, 10));
      Assert.IsNotNull(hover);
      var markup = hover.Contents.MarkupContent;
      Assert.AreEqual(MarkupKind.Markdown, markup.Kind);
      Assert.AreEqual("```dafny\nj: int\n```", markup.Value);
      hover = await RequestHover(documentItem, (1, 15));
      Assert.IsNotNull(hover);
      markup = hover.Contents.MarkupContent;
      Assert.AreEqual(MarkupKind.Markdown, markup.Kind);
      Assert.AreEqual("```dafny\nj: int\n```", markup.Value);
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
      var hover = await RequestHover(documentItem, (5, 7));
      Assert.IsNotNull(hover);
      var markup = hover.Contents.MarkupContent;
      Assert.AreEqual(MarkupKind.Markdown, markup.Kind);
      Assert.AreEqual("```dafny\nx: bool\n```", markup.Value);
      hover = await RequestHover(documentItem, (5, 12));
      Assert.IsNotNull(hover);
      markup = hover.Contents.MarkupContent;
      Assert.AreEqual(MarkupKind.Markdown, markup.Kind);
      Assert.AreEqual("```dafny\nn: nat\n```", markup.Value);
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
      var hover = await RequestHover(documentItem, (1, 7));
      Assert.IsNotNull(hover);
      var markup = hover.Contents.MarkupContent;
      Assert.AreEqual(MarkupKind.Markdown, markup.Kind);
      Assert.AreEqual("```dafny\ni: int\n```", markup.Value);
      hover = await RequestHover(documentItem, (1, 12));
      Assert.IsNotNull(hover);
      markup = hover.Contents.MarkupContent;
      Assert.AreEqual(MarkupKind.Markdown, markup.Kind);
      Assert.AreEqual("```dafny\nn: nat\n```", markup.Value);
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
      var hover = await RequestHover(documentItem, (1, 16));
      Assert.IsNotNull(hover);
      var markup = hover.Contents.MarkupContent;
      Assert.AreEqual(MarkupKind.Markdown, markup.Kind);
      Assert.AreEqual("```dafny\ny: int\n```", markup.Value);
      hover = await RequestHover(documentItem, (1, 33));
      Assert.IsNotNull(hover);
      markup = hover.Contents.MarkupContent;
      Assert.AreEqual(MarkupKind.Markdown, markup.Kind);
      Assert.AreEqual("```dafny\ni: int\n```", markup.Value);
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
      var hover = await RequestHover(documentItem, (0, 22));
      Assert.IsNotNull(hover);
      var markup = hover.Contents.MarkupContent;
      Assert.AreEqual(MarkupKind.Markdown, markup.Kind);
      Assert.AreEqual("```dafny\nr: int\n```", markup.Value);
      hover = await RequestHover(documentItem, (1, 11));
      Assert.IsNotNull(hover);
      markup = hover.Contents.MarkupContent;
      Assert.AreEqual(MarkupKind.Markdown, markup.Kind);
      Assert.AreEqual("```dafny\nr: int\n```", markup.Value);
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
      var hover = await RequestHover(documentItem, (4, 8));
      Assert.IsNotNull(hover);
      var markup = hover.Contents.MarkupContent;
      Assert.AreEqual(MarkupKind.Markdown, markup.Kind);
      Assert.AreEqual("```dafny\nr: Pos\n```", markup.Value);
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
      var hover = await RequestHover(documentItem, (1, 41));
      Assert.IsNotNull(hover);
      var markup = hover.Contents.MarkupContent;
      Assert.AreEqual(MarkupKind.Markdown, markup.Kind);
      Assert.AreEqual("```dafny\ndatatype Position\n```", markup.Value);
    }
  }
}
