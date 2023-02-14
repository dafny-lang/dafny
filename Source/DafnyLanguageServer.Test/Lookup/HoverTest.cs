using System;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.IO;
using System.Linq;
using System.Text.RegularExpressions;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Lookup {
  [TestClass]
  public class HoverTest : ClientBasedLanguageServerTest {

    public override async Task SetUp(Action<DafnyOptions> modifyOptions = null) {
      void ModifyOptions(DafnyOptions options) {
        options.ProverOptions.Add("-proverOpt:SOLVER=noop");
        modifyOptions?.Invoke(options);
      }

      await base.SetUp(ModifyOptions);
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
      if (expectedContent == "null") {
        Assert.IsNull(hover);
        return;
      }
      Assert.IsNotNull(hover);
      var markup = hover.Contents.MarkupContent;
      Assert.IsNotNull(markup);
      Assert.AreEqual(MarkupKind.Markdown, markup.Kind);
      Assert.IsTrue(markup.Value.Contains(expectedContent), "Could not find {1} in {0}", markup.Value, expectedContent);
    }

    /// <summary>
    /// Supported format: A source code interleaved with lines like this:
    /// .... source code ...
    ///      ^[expected content on hovering 's' where newlines are encoded with '\n']
    /// .... source code ...
    /// at the place where a user would hover.
    /// </summary>
    /// <param name="sourceWithHovers"></param>
    private async Task AssertHover(string sourceWithHovers) {
      await WithNoopSolver(async () => {
        sourceWithHovers = sourceWithHovers.TrimStart().Replace("\r", ""); // Might not be necessary
        // Split the source from hovering tasks
        var hoverRegex = new Regex(@"\n\s*(?<ColumnChar>\^)\[(?<ExpectedContent>.*)\](?=\n|$)");
        var source = hoverRegex.Replace(sourceWithHovers, "");
        var hovers = hoverRegex.Matches(sourceWithHovers);
        var documentItem = CreateTestDocument(source);
        client.OpenDocument(documentItem);
        var lineDelta = 0;
        for (var i = 0; i < hovers.Count; i++) {
          var hover = hovers[i];
          var column = hover.Groups["ColumnChar"].Index - (hover.Index + 1);
          var line = sourceWithHovers.Take(hover.Index).Count(x => x == '\n') - (lineDelta++);
          var expectedContent = hover.Groups["ExpectedContent"].Value.Replace("\\n", "\n");
          await AssertHoverContains(documentItem, (line, column), expectedContent);
        }

        Assert.IsTrue(hovers.Count > 0, "No hover expression detected.");
      });
    }

    [TestMethod]
    public async Task HoveringMethodInvocationOfMethodDeclaredInSameDocumentReturnsSignature() {
      await AssertHover(@"
method DoIt() returns (x: int) {
}

method CallDoIt() returns () {
  var x := DoIt();
              ^[```dafny\nmethod DoIt() returns (x: int)\n```]
}");
    }


    [TestMethod]
    public async Task HoveringBoundVariablesFormalsLocalVariablesInMatchExprOrStatement() {
      await AssertHover(@"
datatype DT = A | B | C

method M(dt: DT) {
  match dt {
    case C => 
    case A | B => var x := (y => y)(1); assert x == 1;
                      ^[```dafny\nx: int\n```]
                            ^[```dafny\ny: int\n```]
                                 ^[```dafny\ny: int\n```]
  }
}

method M2(dt: DT) {
  match dt {
    case C => 
    case _ => var x := (y => y)(1); assert x == 1;
                  ^[```dafny\nx: int\n```]
                        ^[```dafny\ny: int\n```]
                             ^[```dafny\ny: int\n```]
  }
}

function F(dt: DT): int {
  match dt {
    case C => 0
    case A | B => var x := (y => y)(1); assert x == 1; 0
                      ^[```dafny\nx: int\n```]
                            ^[```dafny\ny: int\n```]
                                 ^[```dafny\ny: int\n```]
  }
}
function F2(dt: DT): int {
  match dt {
    case C => 0
    case _ => var x := (y => y)(1); assert x == 1; 0
                  ^[```dafny\nx: int\n```]
                        ^[```dafny\ny: int\n```]
                             ^[```dafny\ny: int\n```]
  }
}
");
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
    public async Task HoveringFieldOfSystemTypeReturnsDefinition() {
      await AssertHover(@"
method DoIt() {
  var x := new int[0];
  var y := x.Length;
              ^[```dafny\nconst array.Length: int\n```]
}");
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
      await AssertHover(@"
method DoIt() returns (x: int) {
  return GetX();
            ^[null]
}");
    }

    [TestMethod]
    public async Task HoveringVariableShadowingFieldReturnsTheVariable() {
      await AssertHover(@"
class Test {
  var x: int;

  method DoIt() {
    var x := """";
    print x;
          ^[```dafny\nx: string\n```]
  }
}");
    }

    [TestMethod]
    public async Task HoveringVariableShadowingFieldReturnsTheFieldIfThisIsUsed() {
      await AssertHover(@"
class Test {
  var x: int;

  method DoIt() {
    var x := 1;
    print this.x;
               ^[```dafny\nvar Test.x: int\n```]
  }
}");
    }

    [TestMethod]
    public async Task HoveringVariableShadowingAnotherVariableReturnsTheShadowingVariable() {
      await AssertHover(@"
class Test {
  var x: int;

  method DoIt() {
    var x := 1;
    {
      var x := ""2"";
      print x;
            ^[```dafny\nx: string\n```]
    }
  }
}");
    }

    [TestMethod]
    public async Task HoveringVariableShadowedByAnotherReturnsTheOriginalVariable() {
      await AssertHover(@"
class Test {
  var x: int;

  method DoIt() {
    var x := ""1"";
    {
      var x := 2;
    }
    print x;
          ^[```dafny\nx: string\n```]
  }
}");
    }

    [TestMethod]
    public async Task HoveringTypeOfFieldReturnsTheUserDefinedType() {
      await AssertHover(@"
class A {
  constructor() {}
}

class B {
  var a: A;
         ^[```dafny\nclass A\n```]

  constructor() {
    a := new A();
  }
}");
    }

    [TestMethod]
    public async Task HoveringTypeOfConstructorInvocationReturnsTheUserDefinedType() {
      await AssertHover(@"
class A {
  constructor() {}
}

class B {
  var a: A;

  constructor() {
    a := new A();
             ^[```dafny\nclass A\n```]
  }
}");
    }

    [TestMethod]
    public async Task HoveringParameterOfMethodReturnsTheUserDefinedType() {
      await AssertHover(@"
class A {
  constructor() {}
}

method DoIt(a: A) {}
               ^[```dafny\nclass A\n```]");
    }

    [TestMethod]
    public async Task HoveringParentTraitOfUserDefinedTypeReturnsTheParentTrait() {
      await AssertHover(@"
trait Base {}
class Sub extends Base {}
                   ^[```dafny\ntrait Base\n```]");
    }

    [TestMethod]
    public async Task HoveringParameterDesignatorOfMethodInsideDataTypeReturnsTheParameterType() {
      await AssertHover(@"
datatype SomeType = SomeType {
  method AssertEqual(x: int, y: int) {
    var j:=x == y;
           ^[```dafny\nx: int\n```]
  }
}");
    }

    [TestMethod]
    public async Task HoveringMethodInvocationOfDataTypeReturnsMethodSignature() {
      await AssertHover(@"
datatype SomeType = SomeType {
  method AssertEqual(x: int, y: int) {
    assert x == y;
  }
}

method Main() {
  var instance: SomeType;
  instance.AssertEqual(1, 2);
            ^[```dafny\nmethod SomeType.AssertEqual(x: int, y: int)\n```]
}");
    }

    [TestMethod]
    public async Task HoveringFormalReturnsFormalType() {
      await AssertHover(@"
method f(i: int) {
  var r := i;
           ^[```dafny\ni: int\n```]
}");
    }

    [TestMethod]
    public async Task HoveringDeclarationVariableReturnsInferredVariableType() {
      await AssertHover(@"
method f(i: int) {
  var r := i;
      ^[```dafny\nr: int\n```]
}");
    }

    [TestMethod]
    public async Task HoveringForallBoundVarReturnsBoundVarInferredType() {
      await AssertHover(@"
method f(i: int) {
  var x:=forall j :: j + i == i + j;
                ^[```dafny\nj: int\n```]
                     ^[```dafny\nj: int\n```]
}");
    }

    [TestMethod]
    public async Task HoveringExistsBoundVarReturnsBoundVarInferredType() {
      await AssertHover(@"
method f(i: int) {
  var x:=exists j :: j + i == i;
                ^[```dafny\nj: int\n```]
                     ^[```dafny\nj: int\n```]
}");
    }

    [TestMethod]
    public async Task HoveringSetBoundVarReturnsBoundVarInferredType() {
      await AssertHover(@"
method f(i: int) {
  var x := {1, 2, 3};
  var y := set j | j in x && j < 3;
               ^[```dafny\nj: int\n```]
                   ^[```dafny\nj: int\n```]
}");
    }

    [TestMethod]
    public async Task HoveringMapBoundVarReturnsBoundVarInferredType() {
      await AssertHover(@"
method f(i: int) {
  var m := map j : int | 0 <= j <= i :: j * j;
               ^[```dafny\nj: int\n```]
                              ^[```dafny\nj: int\n```]
}");
    }

    [TestMethod]
    public async Task HoveringLambdaBoundVarReturnsBoundVarInferredType() {
      await AssertHover(@"
method f(i: int) {
  var m := j => j * i;
           ^[```dafny\nj: int\n```]
                ^[```dafny\nj: int\n```]
}");
    }

    [TestMethod]
    public async Task HoveringForAllBoundVarInPredicateReturnsBoundVarInferredType() {
      await AssertHover(@"
predicate f(i: int) {
  forall j :: j + i == i + j
         ^[```dafny\nj: int\n```]
              ^[```dafny\nj: int\n```]
}");
    }

    [TestMethod]
    public async Task HoveringByMethodReturnsInferredType() {
      await AssertHover(@"
predicate even(n: nat)
  ensures even(n) <==> n % 2 == 0 
{
  if n < 2 then n == 0 else even(n - 2)
} by method {
  var x := n % 2 == 0;
      ^[```dafny\nx: bool\n```]
           ^[```dafny\nn: nat\n```]
  return x;
}");
    }

    [TestMethod]
    public async Task HoveringLetInReturnsInferredType() {
      await AssertHover(@"
function test(n: nat): nat {
  var i := n * 2;
      ^[```dafny\ni: int\n```]
           ^[```dafny\nn: nat\n```]
  if i == 4 then 3 else 2
}");
    }

    [TestMethod]
    public async Task HoveringSpecificationBoundVariableReturnsInferredType() {
      await AssertHover(@"
method returnBiggerThan(n: nat) returns (y: int)
  requires var y := 100; forall i :: i < n ==> i < y 
               ^[```dafny\ny: int\n```]
                                ^[```dafny\ni: int\n```]
  ensures forall i :: i > y ==> i > n 
 {
  return n + 2;
}");
    }

    [TestMethod]
    public async Task HoveringResultVarReturnsInferredType() {
      await AssertHover(@"
function f(i: int): (r: int)
                     ^[```dafny\nr: int\n```]
  ensures r - i < 10
          ^[```dafny\nr: int\n```]
{
  i + 2
}");
    }

    [TestMethod]
    public async Task HoverIngInferredVariable() {
      await AssertHover(@"
datatype Pos = Pos(line: int)
function f(i: int): Pos {
  if i <= 3 then Pos(i)
  else
   var r := f(i - 2);
       ^[```dafny\nr: Pos\n```]
   Pos(r.line + 2)
}");
    }

    [TestMethod]
    public async Task HoverIngResultTypeShouldNotCrash() {
      await AssertHover(@"
datatype Position = Position(Line: nat)
function ToRelativeIndependent(): (p: Position)
                                         ^[```dafny\ndatatype Position\n```]
{
   Position(12)
}
");
    }

    [TestMethod]
    public async Task HoveringVariablesInsideNestedMatchStmtWorks() {
      await AssertHover(@"
lemma dummy(e: int) {
  match e {
    case _ => var xx := 1;
                   ^[```dafny\nghost xx: int\n```]
  }
}
method test(opt: int) {
  match(opt)
  case 1 =>
    var s := 1;
        ^[```dafny\ns: int\n```]
}
");
    }
  }
}
