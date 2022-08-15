using System;
using System.Collections.Generic;
using System.Linq;
using System.Diagnostics.Contracts;
using System.IO;
using System.Text.RegularExpressions;
using JetBrains.Annotations;
using Bpl = Microsoft.Boogie;
using BplParser = Microsoft.Boogie.Parser;
using Microsoft.Dafny;
using Microsoft.Dafny.Helpers;
using Xunit;

namespace DafnyPipeline.Test {
  [Collection("Singleton Test Collection - Formatter")]
  public class Formatter {
    enum Newlines {
      LF,
      CR,
      CRLF
    };

    private static Regex indentRegex = new Regex(@"(?<=\n|\r(?!\n))[ \t]*");

    private static Regex removeTrailingNewlineRegex = new Regex(@"(?<=\S|\r|\n)[ \t]+(?=\r?\n|\r(?!\n)|$)");

    private Newlines currentNewlines;

    [Fact]
    public void FormatterWorksForFinalSpaceAfterDatatype() {
      FormatterWorksFor(@"
datatype Maybe<T> = None | Some(get: T)
");
    }

    [Fact]
    public void FormatterWorksForDecreasesInvariantComments() {
      FormatterWorksFor(@"
method Test() {
  while X
    decreases true || false
    // comment
    invariant true || false
    // comment
  {
  }
}
");
    }

    [Fact]
    public void FormatterWorksForAssignments() {
      FormatterWorksFor(@"method test() {
  var
    x
    :=
    1;
  var y := 3;
  x := 2;
  x :=
    3;
  x := 4
    ;
  x
    := 4;
  x
    :=
    4;
  x, y :=
    2, 3;
}");
    }

    [Fact]
    public void FormatterWorksForModulesClassesSpecsForallWhileForLoopIfWhile() {
      FormatterWorksFor(@"
module Test {
  method f1<T, U>(a: T, b: U)
  
  method
    f2<T, U>(a: T, b: U)
  
  method f3
    <T, U>(a: T, b: U)
  
  method f4
    <  T
       // The definition of T
    ,  U>(a: T, b: U)
  
  method f5
    <   T,
        U>(a: T, b: U)
  
  method f6
    <    T,
         U
    >(a: T, b: U)
  
  method f7
    <
      T(00),
      U>(a: T, b: U)
  
  method f8
    <
      T(00),
      U
    >(a: T, b: U)
  
  method f9<
      T, U>(a: T, b: U)
  
  method f10< T
            , U>(a: T, b: U)
  
  method g0(a: int, b: int)
  
  method g1
    (a: int, b: int)
  
  method g2
    (a: int, b: int)
  
  method g3
    (
      a: int, b: int)
  
  method g4
    (
      a: int,
      b: int)
  
  method g5
    (  a: int,
       b: int)
  
  method g6
    (   a: int
    ,   b: int)
  
  method g7(
      a: int,
      b: int)
  
  method g8(
      a: int,
      b: int
    )
  
  method g9(
      a: int
    , b: int
    )
  
  method r1() returns (a: int, b: int) {}
  
  method r2()
    returns (a: int, b: int) {}
  
  method r3() returns
    (a: int, b: int) {}
  
  method r4()
    returns
    (a: int, b: int) {}
  
  method r5()
    returns (
      a: int,
      b: int) {}
  
  method r6()
    returns 
    (   a: int,
        b: int) {}
  
  method r7()
    returns 
    (   a: int
    ,   b: int) {}
  
  method r8()
    returns 
    (   a: int
    ,   b: int
    ) {}
  
  method r9()
    returns 
    (   
      a: int,
      b: int) {}
  
  least lemma l1<T>[
      nat](a: T)
  
  least lemma l3<T>
    [nat]
    (a: T)
  
  least lemma l2<T>[nat
    ](a: T)
  
  /** A comment
    * Followed by newline
    * This is the end */
  module Indented {
    /* Multiline comment
     * should be indented like that
     */
    // Multiple comments
    // One per line
    method Weird()
      returns (x: int)
      // One in the docstring
      ensures &&  x > 1
              && 
                  x > 2
              &&  x > 3 &&
                  x > 4
      ensures
        && x > 5
        && x > 6
      ensures
        x > 7
        && x > 8
      ensures
        x > 9 &&
        x > 10
    {
      x := 11;
    }
    class A {
      static method f() {
        // A comment
        var x := 2;
      }
    }
  }
}

method topLevel(
    x: int,
    y: int
  ) returns (z: int)
  ensures z > 10
  ensures
    && (forall j: int :: j < z || j == x)
    && forall w: int :: w < z
                        && forall j: int :: j < z || j == y
{
  z := 0;
  if z == 0 {
    if
      z == 1
    {
      z := z / 0;
    }
    else
    {
      z := 1;
    }
  } else {
    z := 0;
  }
  forall z <- [0]
    ensures 1 == 1 {
    assert i == 1;
  }
  forall z <- [0]
    ensures 0 == 0
  {
    assert 0 == 0;
  }
  
  forall z <- [0]
    ensures
      0 == 0
  {
    assert 0 != 0;
  }
  while z != 0
    invariant true {
    z := 0;
  }
  while
    z != 0
    invariant true {
    z := 0;
  }
  while
    z != 0
    invariant true
  {
    z := 0;
  }
  for i := 0 to 1 {
    assert i >= 0;
  }
  for i :=
    0 to 1 {
    assert i <= 1;
  }
  for i := 0 to 1
    invariant true
  {
    assert true;
  }
  var x :=
    2;
  var
    x :=
    2;
  var
    x
    ,
    y
    :=
    2
    ,
    3
    ;
  var z
    , 
      w
    :=
    4
    ,
    5
    ;
  var y,
      z
    := x,
       1;
  var b
    , c
    := d
     , e;
  var y
    , z :=
    x
    , 1;
  var
    y,
    z
    :=
    x
    ,1;
  var w :|
    true;
}
// Trailing comments
");
    }

    [Fact]
    public void FormatterWorksForFunctionsIfExprAndMatchCases() {
      FormatterWorksFor(@"
function topLevel(
    x: int,
    y: int
  ): int {
  if x == 2 then
    if x > 3
    then
      y
    else x
  else
    var z := 1;
    var w := z + z;
    assert w != x;
    match x {
      case 1 =>
        17
      case 3 =>
        18
      case y =>
        19 
        +
        match x
        case 17 =>
          12
        case 15 =>
          16 
    }
}");
    }

    [Fact]
    public void FormatterworksForMatchStatementsAndExpressions() {
      FormatterWorksFor(@"
method Test(z: int) {
  match
    z {
    case 0 =>
      match z + 1 {
        case 1 => print ""1"";
                  print ""1bis"";
        case 2 =>
          print ""2"";
          print ""2bis"";
        case 3
          => print ""3"";
             print ""3bis"";
      }
    case
      1 =>
    case 2
      =>
    case 3
      =>
  }
  var x :=match z
          case 1 =>
            var x := 2;
            x
          case 3 => var x := 4;
                    x
          case 5
            => var x := 6;
               x
    ;
  var x :=
    match z {
      case 1 => 2
      case 3 => 4
    };
}
");
    }

    [Fact]
    public void FormatterworksForAssertAssumeExpectPrintReveal() {
      FormatterWorksFor(@"
method Test(z: int) {
  assert z == 1;
  assert z == 1
    ;
  assert
    z == 1
    ;
  assume z == 1;
  assume z == 1
    ;
  assume
    z == 1
    ;
  expect z == 1;
  expect z == 1
    ;
  expect
    z == 1,
    ""error""
    ;
  assert z == 1 by {
    reveal P(), Q(), R();
  }
  assert z == 1 by
  {
    reveal P1(),
           Q1(),
           R1();
  }
  assert z == 2
  by {
    reveal
      P2(),
      Q2(),
      R2();
  }
  
  assert
    z == 3
  by
  // comment here
  {
    reveal  P3()
         ,  Q3()
         ,  R3();
  }
}
");
    }

    [Fact]
    public void FormatWorksForFunctionMethods() {
      FormatterWorksFor(@"
function Test(): int {
  1
} by method {
  var i: nat := 0;
  assert IsScriptForward(edits[..0], |s|) by {
    reveal IsScriptForward();
  }
}");
    }

    [Fact]
    public void FormatWorksConstant() {
      FormatterWorksFor(@"
class T {
  const x
    : int
    := var y := 17;
       y + y
  
  // Comment
}");
    }


    [Fact]
    public void FormatWorksForTypes() {
      FormatterWorksFor(@"
include ""test1""
include
  ""test2""

datatype Color =   Red
                   // Comment1
               |   /** Comment2 */
                   Green
               |   Blue

datatype Color2
  =   Red
      // Comment1
  |   Green   |
      // Comment2
      Blue
      // Blue docstring

// Comment here
datatype T =
    C1()
  | /** C2's comment */
    C2(a: int,
       b: int
       // comment on b
    )
    // C2's comment
  | C3(
      a: int,
      b: int
    , c: int)

datatype D =
  | D1(x: LongType1<
         P1,
         P2>
    )
  | D2( a: int,
        b: LongTypeX< map< int,
                           int>>
      , c: int
    )
  | D3(x: LongType< int,
                    int
       >)

type X = i : int
       | i == 2 || i == 3 witness 2
 
//CommentY
type Y =   i : int
       |   // Comment
           i == 2 || i == 3
           // Comment2
       witness
           // Comment3
           2
           //Comment4

//CommentZ
type Z =
  i : int
  |   i == 2 ||
      i == 3
  witness 2

newtype X
  = i : int
  | || i == 2
    || i == 3 witness var x := 2;
                      x

newtype Y
  =
  i : List<int,
           int>
  | i == 2
    || i == 3
  witness
    var x := 2;
    x

module AM { class A {}
            class B {} }

module
  AN
{  class A {}
   class B {} }

module A {
  import opened B = A
  import
    opened C = A
  import opened
    D = A
  import opened F =
    E
  import opened G
    = E
  import
    opened H =
    B
  import
    opened I
    = B
  import
    opened
    J = B
}

module M {
  export X
    extends A,
            B
    provides L1, L2
    provides L3,
             L4
    provides L5
           , L6
             // Comment
    provides
      L7, L8
    provides
      L9,
      L10
    provides
      L11
      , L12
  export Y
    extends A1
          , B1
    reveals M1, M2
    reveals M3,
            M4
    reveals M5
          , M6
            // Comment
    reveals
      M7, M8
    reveals
      M9,
      M10
    reveals
      M11
      , M12
}
trait X {
  function X(): int {
    1
  }
}
abstract module Abs {
  function X(): int
}
method comprehensions() {
  var x := imap i: int :: i % 2 == 0 := 1;

  var a := imap
             t: int ::  t % 2
                        == 0
                    := 1;

  b := imap
         i: int
       ::
         i % 2 == 0
       :=
         1;

  c := imap i: int |
         i % 4 == 0
       :: i % 2 == 0
       := 1;

  d := imap i: int
         |  i % 5 == 0
       :: i % 2 == 0
       := 1;

  e := imap i: int |  i % 6 == 0
       ::  
         // comment
         i % 2 == 0
       :=  1;
}
iterator Gen(start: int) yields (x: int)
  yield ensures |xs| <= 10 && x == start + |xs| - 1
{
  var i := 0;
  while i < 10 invariant |xs| == i {
    x := start + i;
    yield;
    i := i + 1;
  }
}
");
    }

    [Fact]
    public void FormatterWorksForWhileTests() {
      FormatterWorksFor(@"
method Test() {
  rs.Close();
  ghost var qc := q.contents;
  q := Sort(q);
  assert forall k :: k in q.contents ==> k in multiset(q.contents);
  var wr := new WriterStream;
  wr.Create();

  while 0 < |q.contents|
    invariant wr.Valid() && fresh(wr.footprint)
    invariant glossary.Valid()
    invariant glossary !in wr.footprint
    invariant q !in wr.footprint
    invariant forall k :: k in q.contents ==> k in glossary.keys
  {
    var term := q.Dequeue();
    var r := glossary.Find(term);
    assert r.Some?;
    var definition := r.get;

    // write term with a html anchor
    wr.PutWordInsideTag(term, term);
    var i := 0;

    var qcon := q.contents;
    while i < |definition|
      invariant wr.Valid() && fresh(wr.footprint)
      invariant glossary.Valid()
      invariant glossary !in wr.footprint
      invariant q !in wr.footprint
      invariant qcon == q.contents
      invariant forall k :: k in q.contents ==> k in glossary.keys
    {
      var w := definition[i];
      var r := glossary.Find(w);
      if r == None {
        wr.PutWordInsideHyperlink(w, w);
      } else {
        wr.PutWord(w);
      }
      i:= i +1;
    }
  }
}");
    }

    [Fact]
    public void FormatterWorksForMethodBeforeAClass() {
      FormatterWorksFor(@"
method Test()
  ensures true || false
  // comment should be between ensures and not attached to true/false
  ensures false
{
  assert A !! B; // should not print !!!

  var wr := new WriterStream;
  var definition := r.get;
 
  // write term with a html anchor
  wr.PutWordInsideTag(term, term);

  var i := 0;

  wr.Create();
 
  while 0 < |q.contents|
  
  while (n < N)
    invariant n <= N;
    invariant (forall B: seq<int> ::
               // For any board 'B' with 'N' queens, each placed in an existing row
               |B| == N && (forall i :: 0 <= i && i < N ==> 0 <= B[i] && B[i] < N) &&
               // ... where 'B' is an extension of 'boardSoFar'
               boardSoFar <= B &&
               // ... and the first column to extend 'boardSoFar' has a queen in one of
               // the first 'n' rows
               0 <= B[pos] && B[pos] < n
               ==>
               // ... the board 'B' is not entirely consistent
               (exists p :: 0 <= p && p < N && !IsConsistent(B, p)))
    // comments here
  {
  }
}

function canProveFalse(): bool {
  if 1 == 2 then true
  // Otherwise, we have to make difficult choices
  else if 3 == 4 then true
  // Still not? We give up
  else false
}

class TestClass {
}
");
    }
    [Fact]
    public void FormatterWorksForCppExample() {
      FormatterWorksFor(@"
// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:cpp ExternDefs.h ""%s"" > ""%t""
// RUN: %diff ""%s.expect"" ""%t""

newtype uint32 = i:int | 0 <= i < 0x100000000

method ReturnTuple() returns (x:(uint32,uint32))
{
  return (1, 2);
}

function method EmptyTuple() : () {
  ()
}

function method GetEmptyTuple() : () {
  EmptyTuple()
}

function method Test() : (bool, bool) {
  (false, true)
}

method BoolCallee(a:bool) returns (a0:bool, a1:bool)
{
  return a, a;
}

method BoolCaller(a:bool)
{
  var a0, a1 := BoolCallee(a);
}

method GenericCallee<A>(a:A) returns (a0:A, a1:A)
{
  return a, a;
}

method GenericCaller<A>(a:A)
{
  var a0, a1 := GenericCallee(a);
}

method Main() {
  var x := ReturnTuple();
  var y := x.0;
  print y;
}
");
    }
    [Fact]
    public void FormatterWorksForUniversalPatternShiftDatatypeParens() {
      FormatterWorksFor(@"
newtype b17 = x | 0 <= x < (10 as bv8 << -1) as int
newtype b18 = x | 0 <= x < (10 as bv8 >> -1) as int

method UniversalPattern() {
  var f, _ := Capture(15);
  x := 1 << 2;
  x := 1 >> 3;
}

datatype T = Test
{
}
");
    }
    [Fact]
    public void FormatterworksForAlternatives() {
      FormatterWorksFor(@"
method AlternativeStmt() {
  if
  {
    case x % 2 == 1 =>
      print ""odd"";
    case x % 2 == 0 =>
      print ""even"";
      // That's the last case
  }
  if
  case x % 2 == 1 =>
    print ""odd1"";
  case x % 2 == 0 =>
    print ""even1"";
    // That's the last case
}

method AlternativeLoopStmt() {
  while
    invariant x >= 0
  {
    case x % 2 == 1 =>
      print ""odd2"";
    case x % 2 == 0 =>
      print ""even2"";
      // That's the last case
  }
  while
    invariant x >= 0
  case x % 2 == 1 =>
    print ""odd3"";
  case x % 2 == 0 =>
    print ""even3"";
    // That's the last case
}
");
    }

    private void FormatterWorksFor(string programString) {
      BatchErrorReporter reporter = new BatchErrorReporter();
      var options = DafnyOptions.Create();
      DafnyOptions.Install(options);
      foreach (Newlines newLinesType in Enum.GetValues(typeof(Newlines))) {
        currentNewlines = newLinesType;
        // This formatting test will remove all the spaces at the beginning of the line
        // and then recompute it. The result should be the same string.
        programString = AdjustNewlines(programString);
        var programNotIndented = indentRegex.Replace(programString, "");
        var expectedProgram = removeTrailingNewlineRegex.Replace(programString, "");

        ModuleDecl module = new LiteralModuleDecl(new DefaultModuleDecl(), null);
        Microsoft.Dafny.Type.ResetScopes();
        BuiltIns builtIns = new BuiltIns();
        Parser.Parse(programNotIndented, "virtual", "virtual", module, builtIns, reporter);
        var dafnyProgram = new Program("programName", module, builtIns, reporter);
        if (reporter.ErrorCount > 0) {
          var error = reporter.AllMessages[ErrorLevel.Error][0];
          Assert.False(true, $"{error.message}: line {error.token.line} col {error.token.col}");
        }
        var reprinted = TokenFormatter.__default.printSourceReindent(dafnyProgram.GetFirstTopLevelToken(),
          IndentationFormatter.ForProgram(dafnyProgram));
        if (expectedProgram != reprinted && HelperString.Debug) {
          Console.Write(reprinted);
        }
        Assert.Equal(expectedProgram, reprinted);

        // Verify that the formatting is stable.
        module = new LiteralModuleDecl(new DefaultModuleDecl(), null);
        Microsoft.Dafny.Type.ResetScopes();
        builtIns = new BuiltIns();
        Parser.Parse(reprinted, "virtual", "virtual", module, builtIns, reporter);
        dafnyProgram = new Program("programName", module, builtIns, reporter);
        Assert.Equal(0, reporter.ErrorCount);
        var reprinted2 = TokenFormatter.__default.printSourceReindent(dafnyProgram.GetFirstTopLevelToken(),
          IndentationFormatter.ForProgram(dafnyProgram));
        Assert.Equal(reprinted, reprinted2);
      }
    }

    private string AdjustNewlines(string programString) {
      return currentNewlines switch {
        Newlines.LF => new Regex("\r?\n").Replace(programString, "\n"),
        Newlines.CR => new Regex("\r?\n").Replace(programString, "\r"),
        _ => new Regex("\r?\n").Replace(programString, "\r\n")
      };
    }

    private void AssertTrivia(TopLevelDecl topLevelDecl, string triviaBefore, string triviaDoc) {
      Assert.Equal(AdjustNewlines(triviaBefore), topLevelDecl.StartToken.LeadingTrivia);
      Assert.Equal(AdjustNewlines(triviaDoc), topLevelDecl.TokenWithTrailingDocString.TrailingTrivia);
    }

    private void AssertTrivia(MemberDecl topLevelDecl, string triviaBefore, string triviaDoc) {
      Assert.Equal(AdjustNewlines(triviaBefore), topLevelDecl.StartToken.LeadingTrivia);
      Assert.Equal(AdjustNewlines(triviaDoc), topLevelDecl.TokenWithTrailingDocString.TrailingTrivia);
    }
  }
}
