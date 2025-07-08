﻿using System;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Extensions;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using System.IO;
using System.Linq;
using System.Text.RegularExpressions;
using System.Threading.Tasks;
using JetBrains.Annotations;
using Microsoft.Dafny.LanguageServer.IntegrationTest.Util;
using OmniSharp.Extensions.JsonRpc.Server;
using Xunit.Abstractions;
using Xunit;
using XunitAssertMessages;

namespace Microsoft.Dafny.LanguageServer.IntegrationTest.Lookup {
  public class HoverTest : ClientBasedLanguageServerTest {
    protected override async Task SetUp(Action<DafnyOptions> modifyOptions = null) {
      void ModifyOptions(DafnyOptions options) {
        options.ProverOptions.Add("SOLVER=noop");
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

    private async Task AssertHoverContains(TextDocumentItem documentItem, Position hoverPosition, string expectedContent) {
      var hover = await RequestHover(documentItem, hoverPosition);
      if (expectedContent == "null" || expectedContent == null) {
        Assert.Null(hover);
        return;
      }
      AssertM.NotNull(hover, $"No hover message found at {hoverPosition}, was supposed to display {expectedContent}");
      var markup = hover.Contents.MarkupContent;
      Assert.NotNull(markup);
      Assert.Equal(MarkupKind.Markdown, markup.Kind);
      Assert.True(markup.Value.Contains(expectedContent), $"Could not find '{expectedContent}'\n in \n'{markup.Value}'");
    }

    /// <summary>
    /// Supported format: A source code interleaved with lines like this:
    /// .... source code ...
    ///      ^[expected content on hovering 's' where newlines are encoded with '\n']
    /// .... source code ...
    /// at the place where a user would hover.
    /// </summary>
    /// <param name="sourceWithHovers"></param>
    /// <param name="modifyOptions"></param>
    private async Task AssertHover(string sourceWithHovers, bool useProjectFile, [CanBeNull] Action<DafnyOptions> modifyOptions = null) {
      await SetUp(o => {
        o.ProverOptions.Add("SOLVER=noop");
        if (modifyOptions != null) {
          modifyOptions(o);
        }
      });
      sourceWithHovers = sourceWithHovers.TrimStart().Replace("\r", ""); // Might not be necessary
      // Split the source from hovering tasks
      var hoverRegex = new Regex(@"\n//\s*(?<ColumnChar>\^)\[(?<ExpectedContent>.*)\](?=\n|$)");
      var source = hoverRegex.Replace(sourceWithHovers, "");
      var hovers = hoverRegex.Matches(sourceWithHovers);
      var documentItem = CreateTestDocument(source, "AssertHover.dfy");
      if (useProjectFile) {
        await CreateOpenAndWaitForResolve("", Path.Combine(Path.GetDirectoryName(documentItem.Uri.GetFileSystemPath())!, DafnyProject.FileName));
      }
      client.OpenDocument(documentItem);
      var lineDelta = 0;
      for (var i = 0; i < hovers.Count; i++) {
        var hover = hovers[i];
        var column = hover.Groups["ColumnChar"].Index - (hover.Index + 1);
        var line = sourceWithHovers.Take(hover.Index).Count(x => x == '\n') - (lineDelta++);
        var expectedContent = hover.Groups["ExpectedContent"].Value.Replace("\\n", "\n");
        await AssertHoverContains(documentItem, (line, column), expectedContent);
      }

      Assert.True(hovers.Count > 0, "No hover expression detected.");
    }

    [Fact]
    public async Task Crash() {
      var source = @"
module M {
  method m()
}
module P refines M {
  method m ... {
    while true { ...; }
  }
}";

      var document = CreateAndOpenTestDocument(source);
      var hoverResult = await client.RequestHover(new HoverParams() {
        Position = new Position(0, 20),
        TextDocument = document
      }, CancellationToken);
      Assert.Null(hoverResult);
    }

    [Fact]
    public async Task RecoverableParseErrorTypeRhs() {
      var markup = @"
class Bla { }

method Foo() {
  var ><x := new Bla();
}
/".TrimStart();
      MarkupTestFile.GetPositionAndRanges(markup, out var source, out var position, out _);
      var document = CreateTestDocument(source);
      client.OpenDocument(document);
      var hoverResult = await client.RequestHover(new HoverParams() {
        Position = position,
        TextDocument = document
      }, CancellationToken);
      Assert.Contains("No hover information available", hoverResult.ToString());
    }

    [Fact]
    public async Task RecoverableParseError() {
      var document = await CreateOpenAndWaitForResolve(@"
class Foo {
  const x := '\U2345'
//      ^[```dafny\nconst x: ?\n```]
}".TrimStart());
      await AssertHoverContains(document, new Position(1, 8), "No hover information available due to program error");
    }

    [Fact]
    public async Task HoveringMethodInvocationOfMethodDeclaredInSameDocumentReturnsSignature() {
      await AssertHover(@"
method DoIt() returns (x: int) {
}

method CallDoIt() returns () {
  var x := DoIt();
//            ^[```dafny\nmethod DoIt() returns (x: int)\n```]
}", true);
    }

    [Fact]
    public async Task HoveringBoundVariablesFormalsLocalVariablesInMatchExprOrStatement() {
      await AssertHover(@"
datatype DT = A | B | C

method M(dt: DT) {
  match dt {
    case C => 
    case A | B => var x := (y => y)(1); assert x == 1;
//                    ^[```dafny\nx: int\n```]
//                          ^[```dafny\ny: int\n```]
//                               ^[```dafny\ny: int\n```]
  }
}

method M2(dt: DT) {
  match dt {
    case C => 
    case _ => var x := (y => y)(1); assert x == 1;
//                ^[```dafny\nx: int\n```]
//                      ^[```dafny\ny: int\n```]
//                           ^[```dafny\ny: int\n```]
  }
}

function F(dt: DT): int {
  match dt {
    case C => 0
    case A | B => var x := (y => y)(1); assert x == 1; 0
//                    ^[```dafny\nx: int\n```]
//                          ^[```dafny\ny: int\n```]
//                               ^[```dafny\ny: int\n```]
  }
}
function F2(dt: DT): int {
  match dt {
    case C => 0
    case _ => var x := (y => y)(1); assert x == 1; 0
//                ^[```dafny\nx: int\n```]
//                      ^[```dafny\ny: int\n```]
//                           ^[```dafny\ny: int\n```]
  }
}
", false);
    }

    [Fact]
    public async Task HoverReturnsBeforeVerificationIsComplete() {
      var documentItem = CreateTestDocument(NeverVerifies, "HoverReturnsBeforeVerificationIsComplete.dfy");
      await client.OpenDocumentAndWaitAsync(documentItem, CancellationToken);

      var verificationTask = GetLastDiagnostics(documentItem);
      var definitionTask = RequestHover(documentItem, (4, 14));
      var first = await Task.WhenAny(verificationTask, definitionTask);
      Assert.False(verificationTask.IsCompleted);
      AssertM.Same(first, definitionTask, first.ToString());
    }

    [Fact]
    public async Task HoveringFieldOfSystemTypeReturnsDefinition() {
      await AssertHover(@"
method DoIt() {
  var x := new int[0];
  var y := x.Length;
//            ^[```dafny\nconst array.Length: int\n```]
}", true);
    }

    [Fact]
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

    [Fact]
    public async Task HoveringInvocationOfUnknownFunctionOrMethodReturnsNull() {
      await AssertHover(@"
method DoIt() returns (x: int) {
  return GetX();
//          ^[null]
}", false);
    }

    [Fact]
    public async Task HoveringVariableShadowingFieldReturnsTheVariable() {
      await AssertHover(@"
class Test {
  var x: int;

  method DoIt() {
    var x := """";
    print x;
//        ^[```dafny\nx: string\n```]
  }
}", true);
    }

    [Fact]
    public async Task HoveringVariableShadowingFieldReturnsTheFieldIfThisIsUsed() {
      await AssertHover(@"
class Test {
  var x: int;

  method DoIt() {
    var x := 1;
    print this.x;
//             ^[```dafny\nvar Test.x: int\n```]
  }
}", false);
    }

    [Fact]
    public async Task HoveringVariableShadowingAnotherVariableReturnsTheShadowingVariable() {
      await AssertHover(@"
class Test {
  var x: int;

  method DoIt() {
    var x := 1;
    {
      var x := ""2"";
      print x;
//          ^[```dafny\nx: string\n```]
    }
  }
}", true);
    }

    [Fact]
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
//        ^[```dafny\nx: string\n```]
  }
}", false);
    }

    [Fact]
    public async Task HoveringTypeOfFieldReturnsTheUserDefinedType() {
      await AssertHover(@"
class A {
  constructor() {}
}

class B {
  var a: A;
//       ^[```dafny\nclass A\n```]

  constructor() {
    a := new A();
  }
}", true);
    }

    [Fact]
    public async Task HoveringTypeOfConstructorInvocationReturnsTheUserDefinedType() {
      await AssertHover(@"
class A {
  constructor() {}
}

class B {
  var a: A;

  constructor() {
    a := new A();
//           ^[```dafny\nconstructor A()\n```]
  }
}", false);
    }

    [Fact]
    public async Task HoveringParameterOfMethodReturnsTheUserDefinedType() {
      await AssertHover(@"
class A {
  constructor() {}
}

method DoIt(a: A) {}
//             ^[```dafny\nclass A\n```]", true);
    }

    [Fact]
    public async Task HoveringParentTraitOfUserDefinedTypeReturnsTheParentTrait() {
      await AssertHover(@"
trait Base {}
class Sub extends Base {}
//                 ^[```dafny\ntrait Base\n```]", false);
    }

    [Fact]
    public async Task HoveringParameterDesignatorOfMethodInsideDataTypeReturnsTheParameterType() {
      await AssertHover(@"
datatype SomeType = SomeType {
  method AssertEqual(x: int, y: int) {
    var j:=x == y;
//         ^[```dafny\nx: int\n```]
  }
}", true);
    }

    [Fact]
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
//          ^[```dafny\nmethod SomeType.AssertEqual(x: int, y: int)\n```]
}", false);
    }

    [Fact]
    public async Task HoveringFormalReturnsFormalType() {
      await AssertHover(@"
method f(i: int) {
  var r := i;
//         ^[```dafny\ni: int\n```]
}", true);
    }

    [Fact]
    public async Task HoveringDeclarationVariableReturnsInferredVariableType() {
      await AssertHover(@"
method f(i: int) {
  var r := i;
//    ^[```dafny\nr: int\n```]
}", false);
    }

    [Fact]
    public async Task HoveringForallBoundVarReturnsBoundVarInferredType() {
      await AssertHover(@"
method f(i: int) {
  var x:=forall j :: j + i == i + j;
//              ^[```dafny\nj: int\n```]
//                   ^[```dafny\nj: int\n```]
}", true);
    }

    [Fact]
    public async Task HoveringExistsBoundVarReturnsBoundVarInferredType() {
      await AssertHover(@"
method f(i: int) {
  var x:=exists j :: j + i == i;
//              ^[```dafny\nj: int\n```]
//                   ^[```dafny\nj: int\n```]
}", false);
    }

    [Fact]
    public async Task HoveringSetBoundVarReturnsBoundVarInferredType() {
      await AssertHover(@"
method f(i: int) {
  var x := {1, 2, 3};
  var y := set j | j in x && j < 3;
//             ^[```dafny\nj: int\n```]
//                 ^[```dafny\nj: int\n```]
}", true);
    }

    [Fact]
    public async Task HoveringMapBoundVarReturnsBoundVarInferredType() {
      await AssertHover(@"
method f(i: int) {
  var m := map j : int | 0 <= j <= i :: j * j;
//             ^[```dafny\nj: int\n```]
//                            ^[```dafny\nj: int\n```]
}", false);
    }

    [Fact]
    public async Task HoveringLambdaBoundVarReturnsBoundVarInferredType() {
      await AssertHover(@"
method f(i: int) {
  var m := j => j * i;
//         ^[```dafny\nj: int\n```]
//              ^[```dafny\nj: int\n```]
}", true);
    }

    [Fact]
    public async Task HoveringForAllBoundVarInPredicateReturnsBoundVarInferredType() {
      await AssertHover(@"
ghost predicate f(i: int) {
  forall j :: j + i == i + j
//       ^[```dafny\nj: int\n```]
//            ^[```dafny\nj: int\n```]
}", false);
    }

    [Fact]
    public async Task HoveringByMethodReturnsInferredType() {
      await AssertHover(@"
predicate even(n: nat)
  ensures even(n) <==> n % 2 == 0 
{
  if n < 2 then n == 0 else even(n - 2)
} by method {
  var x := n % 2 == 0;
//    ^[```dafny\nx: bool\n```]
//         ^[```dafny\nn: nat\n```]
  return x;
}", true);
    }

    [Fact]
    public async Task HoveringLetInReturnsInferredType() {
      await AssertHover(@"
function test(n: nat): nat {
  var i := n * 2;
//    ^[```dafny\ni: int\n```]
//         ^[```dafny\nn: nat\n```]
  if i == 4 then 3 else 2
}", false);
    }

    [Fact]
    public async Task HoveringSpecificationBoundVariableReturnsInferredType() {
      await AssertHover(@"
method returnBiggerThan(n: nat) returns (y: int)
  requires var y := 100; forall i :: i < n ==> i < y 
//             ^[```dafny\ny: int\n```]
//                              ^[```dafny\ni: int\n```]
  ensures forall i :: i > y ==> i > n 
 {
  return n + 2;
}", true);
    }

    [Fact]
    public async Task HoveringResultVarReturnsInferredType() {
      await AssertHover(@"
function f(i: int): (r: int)
//                   ^[```dafny\nr: int\n```]
  ensures r - i < 10
//        ^[```dafny\nr: int\n```]
{
  i + 2
}", false);
    }

    [Fact]
    public async Task HoverIngInferredVariable() {
      await AssertHover(@"
datatype Pos = Pos(line: int)
function f(i: int): Pos {
  if i <= 3 then Pos(i)
  else
   var r := f(i - 2);
//     ^[```dafny\nr: Pos\n```]
   Pos(r.line + 2)
}", true);
    }

    [Fact]
    public async Task HoverIngResultTypeShouldNotCrash() {
      await AssertHover(@"
datatype Position = Position(Line: nat)
function ToRelativeIndependent(): (p: Position)
//                                       ^[```dafny\ndatatype Position\n```]
{
   Position(12)
}
", false);
    }

    [Fact]
    public async Task HoveringVariablesInsideNestedMatchStmtWorks() {
      await AssertHover(@"
lemma dummy(e: int) {
  match e {
    case _ => var xx := 1;
//                 ^[```dafny\nghost xx: int\n```]
  }
}
method test(opt: int) {
  match(opt)
  case 1 =>
    var s := 1;
//      ^[```dafny\ns: int\n```]
}
", true);
    }

    public HoverTest(ITestOutputHelper output) : base(output) {
    }

    [Fact]
    public async Task HoverShouldDisplayComments() {
      await AssertHover(@"
predicate pm()
  // No comment for pm
{ true }

/** Rich comment
  * @param k The input
  *          that is ignored
  * @param l The second input that is ignored
  * @returns 1 no matter what*/
function g(k: int, l: int): int { 1 }

/** A comment for pt */
twostate predicate pt() { true }

least predicate pl()
  // A comment for pl
{ true }

/** A comment for pg
  * That spans two lines */
greatest predicate pg() { true }

/** Returns an integer without guarantee
  * @returns The integer
  */
method m() returns (i: int) { i := *; }

/** The class C. Should be used like this:
  * ```dafny
  * new C();
  * ```
  */
class C {
  // Unformatted comment
  static method m() {}

  /** This is the constructor 
  */
  constructor() {}

  /** Should be the number of x in C */
  var x: int

  const X: int // The expected number of x
}

function f(): int
  /** Rich comment
    * @returns 1 no matter what
    */
{ 1 }

/** Rich comment for D */
datatype D = DD(value: int)

/* D whose value is even */
type T = x: D | x.value % 2 == 0 witness DD(0)

/* Even numbers hidden in a newtype */
newtype Even = x: int | x % 2 == 0

/** A useful lemma */
lemma lem() {}

/** A useful greatest lemma */
greatest lemma greatestLemma() {}

/** A useful least lemma */
least lemma leastLemma() {}

/** A useful twostate lemma */
twostate lemma twostateLemma() {}

method test(d: D, t: T, e: Even) {
//             ^[Rich comment for D]
 //                   ^[D whose value is even] // Not working yet
 //                         ^[Even numbers hidden in a newtype] // Not working yet
  var x1 := pm();
//          ^[No comment for pm]
  var x2 := pg();
//          ^[A comment for pg\nThat spans two lines]
  var x3 := pl();
//          ^[A comment for pl]
  var x4 := pt();
//          ^[A comment for pt]
  var xg := g(0, 1);
//          ^[Rich comment\n@param k The input\n         that is ignored\n@param l The second input that is ignored\n@returns 1 no matter what]
  C.m(); // TODO
 //  ^[Unformatted comment] // Does not work yet.
  var c: C := new C();
//                ^[This is the constructor\n```dafny\nconstructor C()\n```]
  var xc := c.x;
//            ^[Should be the number of x in C]
  var xx := c.X;
//            ^[The expected number of x]
  var xf := f();
//          ^[Rich comment\n@returns 1 no matter what]
  lem();
//^[A useful lemma]
  greatestLemma();
//^[A useful greatest lemma]
  leastLemma();
//^[A useful least lemma]
  twostateLemma();
//^[A useful twostate lemma]
}", true);
      await AssertHover(@"
/** Rich comment
  * @param k The input
  *          that is ignored
  * @param l The second input that is ignored
  * @returns 1 no matter what*/
function g(k: int, l: int): int { 1 }

/** Returns an integer without guarantee
  * @returns The integer
  */
method m() returns (i: int) { i := *; }

function f(): int
  /** Rich comment
    * @returns 1 no matter what
    */
{ 1 }

method test() {
  var xg := g(0, 1);
//          ^[Rich comment\n|  |  |\n| --- | --- |\n| **Params** | **k** - The input<br>         that is ignored |\n| | **l** - The second input that is ignored |\n| **Returns** | 1 no matter what |]
  var i := m();
//         ^[Unformatted comment] // Does not work yet.
  var xf := f();
//          ^[Rich comment\n|  |  |\n| --- | --- |\n| **Returns** | 1 no matter what |]
}", true, o => o.Set(InternalDocstringRewritersPluginConfiguration.UseJavadocLikeDocstringRewriterOption, true));
    }
  }
}
