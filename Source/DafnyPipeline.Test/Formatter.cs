using System;
using System.Collections;
using System.Collections.Generic;
using System.Linq;
using System.Diagnostics.Contracts;
using System.IO;
using System.Text.RegularExpressions;
using JetBrains.Annotations;
using Bpl = Microsoft.Boogie;
using BplParser = Microsoft.Boogie.Parser;
using Microsoft.Dafny;
using Xunit;

namespace DafnyPipeline.Test {

  // Simple test cases (FormatterWorksFor with only one argument)
  // consist of removing all the indentation from the program,
  // adding it through the formatter, and checking if we obtain the initial result
  //
  // Advanced test cases consist of passing the program and its expected result after indentation
  //
  // Every test is performed with all three newline styles
  // Every formatter program is formatted again to verify that it stays the same.
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
    public void FormatterWorksForArguments() {
      FormatterWorksFor(@"
method Test()
{
  me(func(arg(3,
              4)));

  me(func(arg(5,
              6
             ,7
          )
     )
  );

  me(func(arg(
            8, 9)));

  me(func(
       arg(
         10, 11)));

  me(
    func(
      arg(
        12, 13)),
    func2());
  me
  (func
   (arg
    (1
    ,2)),
   func2());
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
    public void FormatterWorksForMethodsInModule() {
      FormatterWorksFor(@"
import opened Test
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
  
}");
    }

    [Fact]
    public void FormatterWorksForCommentsAndAlignmentAmpStatements() {
      FormatterWorksFor(@"
module Test {
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
      
      ensures Binds(x) ==
              Bind(y)
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
function Zipper2<T>(a: List<T>, b: List<T>)
  : List<T>
  decreases /* max(a,b) */ if a < b then b else a,
            /* min(a,b) */ if a < b then a else b
{
  match a
  case Nil => b
  case Cons(x, c) => List.Cons(x, Zipper2(b, c))
}
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
        17 // This is the expected result

      // This case is particularly useful
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
    public void FormatterWorksForCaseComments() {
      FormatterWorksFor(@"
predicate SmallOdd(i: int) {
  match i
  // Case small odd
  case 1 => true
  case 3 => true
  // case small even
  case 0 => false
  /* Nested /*case*/ comment */
  case 2 => false
  /* All other cases */
  case i => SmallOdd(i-2)
}
method SmallOdd(i: int) returns (j: bool) {
  match i
  // Case small odd
  case 1 =>
    j := true;
  case 3 => 
    j := true;
  // case small even
  case 0 =>
    j := false;
  case 2 =>
    j := false;
  /* All other cases */
  case i =>
    j := SmallOdd(i-2);
}
");
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
  
  var x :=(match z
           case 1 =>
             var x := 2;
             x
           case 3 => var x := 4;
                     x
           case 5
             => var x := 6;
                x
          );
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
    public void FormatWorksForChainedImplications() {
      FormatterWorksFor(@"
method Test() {
  assert (1 ==>
            2 ==> 
              3);
  assert (4
          ==> 5
            ==> 6);
  assert (7
          <== 8 
          <== 9);
  assert (10 <==
          11 <== 
          12);
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
    public void FormatWorksForSingleInclude() {
      FormatterWorksFor(@"
// RUN

include ""git-issue48-include.dfyi""

");
    }

    [Fact]
    public void FormatWorksForFirstNestedElephantAssignments() {
      FormatterWorksFor(@"
function TestExpressionParsing(b: bool, n: nat, o1: NatOutcome, o2: NatOutcome): NatOutcome {
  var expr1: nat :- (var x := if b then o1 else o2; x);
  var use_expr1: nat := expr1;
  var expr2 :- (var x := if b then o1 else o2; x);
  var use_expr2: nat := expr2;
  o2
}
");
    }

    [Fact]
    public void FormatWorksForMatchExpression() {
      FormatterWorksFor(@"
predicate bad(e:Maybe)
{
  forall i :: 0 <= i < 1 ==>
                0 == match e
                     case Nothing =>
                       0
                     case Just => 0
}
predicate bad2(e:Maybe)
{
  forall i ::
    0 <= i < 1 ==>
      0 == match e case Nothing => 0
                   case Just => 0
}");
    }

    [Fact]
    public void FormatterWorksForIteratorRequiresComment() {
      FormatterWorksFor(@"
iterator Iter(x: int) yields (y: int)
  requires A: 0 <= x
  // yield requires B: 0 <= y  // not allowed; won't parse
{
}
");
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
type NoWitness_EffectlessArrow<!A(!new), B> = f: A ~> B  // error: cannot find witness
  | forall a :: f.reads(a) == {}
 
type X = i : int
  | i == 2 || i == 3 witness 2
 
//CommentY
type Y =   i : int
  | // Comment
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

newtype y = int

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

    [Fact]
    public void FormatterWorksForAlignedSingleLineTrailingComments() {
      var before = @"
module RefinedF refines BaseF {
  function f(): bool { false } // OK. Local f preferred over imported f
                               // even if imported into refinement parent
  lemma A() {
  forall u: int {  // regression: the inferred ensures clause used to have
                   // a problem with static const fields
    B(u);
  }
  }

  method DeclWithHavoc()
  {
    var b: int := *;  // error: technically fine, since b is never used, but here the compiler
// This comment should be on its own line
  }
}";
      var after = @"
module RefinedF refines BaseF {
  function f(): bool { false } // OK. Local f preferred over imported f
                               // even if imported into refinement parent
  lemma A() {
    forall u: int {  // regression: the inferred ensures clause used to have
                     // a problem with static const fields
      B(u);
    }
  }

  method DeclWithHavoc()
  {
    var b: int := *;  // error: technically fine, since b is never used, but here the compiler
    // This comment should be on its own line
  }
}";
      FormatterWorksFor(before, after);
    }



    [Fact]
    public void FormatterWorksForModifyStatements() {
      FormatterWorksFor(@"
method Test() {
  modify x {
    x := 2;
  }
  modify y,
         x
       , z
  {
    z := 2;
  }

  modify
    y,
    x
    , z
  {
    z := 2;
  }
}
");
    }

    [Fact]
    public void FormatterWorksForModules() {
      FormatterWorksFor(@"
module Tests {
class C {
  function F(c: C, d: D): bool { true }
  method M(x: int)
  { }
}
}", @"
module Tests {
  class C {
    function F(c: C, d: D): bool { true }
    method M(x: int)
    { }
  }
}");
    }

    [Fact]
    public void FormatterWorksForElephantOperatorWithoutLHS() {
      FormatterWorksFor(@"
method {:test} PassingTestUsingNoLHSAssignOrHalt() {
  :- // Comment 
    expect FailUnless(true);
  :-
    expect FailUnless(true);
}");
    }

    [Fact]
    public void FormatterWorksForPrintStmt() {
      FormatterWorksFor(@"
// Sanity check
method Main() {
  print FunctionMethodSyntax.CompiledFunction()
        + GhostFunctionSyntax.CompiledFunction()
        + StillGhostFunctionSyntax.CompiledFunction()
        + BackToDefault.CompiledFunction();
  
  print
    NFunctionMethodSyntax.CompiledFunction()
    + NGhostFunctionSyntax.CompiledFunction()
    + NStillGhostFunctionSyntax.CompiledFunction()
    + NBackToDefault.CompiledFunction();
}
");
    }

    [Fact]
    public void FormatterworksForIteratorsAfterDatatypes() {
      FormatterWorksFor(@"
datatype MG5 =  MG5(ghost x: int, y: int := FG(x), ghost z: int := FC(x), w: int := FC(x)) // error: call to FC passes in a ghost expression
iterator        MG6(      x: int, y: int := FG(x), ghost z: int := FC(x), w: int := FC(x))
iterator        MG7(ghost x: int, y: int := FG(x), ghost z: int := FC(x), w: int := FC(x)) // error: call to FC passes in a ghost expression

iterator Iter0(x: int := y, y: int := 0)
  requires true
  yield requires true
{ }
");
    }

    [Fact]
    public void FormatterWorksForVarsAndGhostVarsAndUnchanged() {
      FormatterWorksFor(@"
twostate predicate BadVariations(c: Twostate, d: Twostate, e: Twostate, f: Twostate)
{
  && unchanged(
       this,
       c
     )
  && old(
       c.c
     ) == c.c
  && fresh(
       c.c
     )
  && allocated(
       c.c
     )
}
lemma LeftIdentity<A,B>(x : A, f : A -> M<B>)
  ensures Bind(Return(x), f) == f(x)
{
  var State(h) := State(s => (x, s));
  var State(g2) := f(x);
  var x := new A[2](i =>
                    i + 1);
  calc {}
}

function Fu(): int
{
  ghost var p: () -> bool := P;  // error: cannot use a two-state function in this context
  ghost var q: () -> bool := YY.Sp;  // error: cannot use a two-state function in this context
  if P() then 5 else 7  // error: cannot use a two-state function here
}
");
    }

    [Fact]
    public void FormatterWorksForIfCaseReturn() {
      FormatterWorksFor(@"
method Test() {
  if
  case true =>
    var a := c.Plus(0);  // error: c not allocated in old state
  case true =>
    var a := c.Plus@A(0);  // error: c not allocated in state A
    return 2;
}
");
    }


    [Fact]
    public void FormatterWorksForElephantOperatorInMatch() {
      FormatterWorksFor(@"
method execute_external_method(n:nat, m:nat) returns (r:Status)
{
  match n { // match statement is essential to reproduce the bug
    case 0 =>            
      :- Func1(); // elephant operator is essential to reproduce the bug
      match m {
        case 1 =>
          :- Func1();
        case _ =>
          return Success;
      }
    case _ =>
      return Success;
  }
}
");
    }

    [Fact]
    public void FormatterWorksForBraceAfterArrowAndSimilar() {
      FormatterWorksFor(@"
function Test(): int {
  match s
  case None => (
    var x := 2;
    x
  )
  case Some => (
    match m
    case O => 1
  )
}
method Test() {
  match s {
    case
      1 => {
      print ""k"";
    }
    case 2
      =>
    case 3 => {
    }
  }
}
");
    }

    [Fact]
    public void FormatterWorksForEmptyDocument() {
      FormatterWorksFor(@"
/*
module S0 refines R {
  // This module defines a local g().  It takes precedence over the g() that
  // comes from the (inherited) opened import

  // this is no longer possible due to too many potential clashes and generally
  // weird behaviour

  function g(): int { 2 }
*/
", null, true);
    }

    [Fact]
    public void FormatterWorksForLongCommentsDocument() {
      var testCase = @"
module R {
  /* Simple comment
   * in a module
   */
  import opened LibA
}
/*
module S0 refines R {
  var x := 2
    * 3;
  // This module defines a local g().  It takes precedence over the g() that
  // comes from the (inherited) opened import
  // this is no longer possible due to too many potential clashes and generally
  // weird behaviour

  function g(): int { 2 }
*/
module V {
  /** doclike comment
    * in a module
    */
  import opened LibA
  function g(): int { 4 }
}
";
      FormatterWorksFor(testCase, testCase);
    }

    [Fact]
    public void FormatterworksForRefinedMethod() {
      FormatterWorksFor(@"
method M... 
{
  if ... {}
  else if (x == y) {}
  else {}
}
");
    }

    [Fact]
    public void FormatterWorksForMultipleModules() {
      FormatterWorksFor(@"
module Outer.A {
  import B
  import C
  const a := B.b + C.c
}");
    }

    [Fact]
    public void FormatterWorksForLabelsBeforeIf() {
      FormatterWorksFor(@"

method TheBreaker_AllGood(M: int, N: int, O: int)
{
  label MyLabelBlock:
  label MyLabelBlockAgain:
  if (*) {
    a := 15; break;
  }
  assert M <= i || b == 12 || e == 37;
}
");
    }

    [Fact]
    public void FormatterWorksForSkeletonStatement() {
      FormatterWorksFor(@"
module ModifyStmtBreak1 refines ModifyStmtBreak0 {
  method W... {
    while true
      ...
    while ...
      invariant k == x;
    {
      k := k + 1;
    }
    modify ... {
      if * {
        break;
      } else {
        break L;
      }
    }
  }
}
");
    }

    [Fact]
    public void FormatterWorksForDividedBlockStmt() {
      FormatterWorksFor(@"
class X {
  constructor Init(x: nat)
  {
    modify `c;
    new;
    a := a + b;
  }
}
");
    }

    [Fact]
    public void FormatterWorksForDatatypeWithVerticalBarAfterwardsOrOneLine() {
      FormatterWorksFor(@"
datatype Lindgren =
  Pippi(Node) |
  Longstocking(seq<object>, Lindgren) |
  HerrNilsson

datatype Logical =
  Iff // And, Or, and Imp are in LazyOp
datatype Eq =
  EqCommon | NeqCommon
");
    }

    [Fact]
    public void FormatterWorksForHintsInCalcStatements() {
      FormatterWorksFor(@"
class Test {
  ghost constructor CalcInInitializationPhase() {
    var c0 := new Cell; // fine here
    var g0 := new G(5); // fine here
    calc {
      5;
    ==  { var c1 := new Cell; // error: cannot allocate inside calc hint
          var g1 := new G(5); // error: cannot allocate inside calc hint
        }
      2 + 3;
    }
    assert true by {
      var c2 := new Cell; // error: cannot allocate inside assert-by
      var g2 := new G(5); // error: cannot allocate inside assert-by
    }
    new;
  }
}
");
    }

    [Fact]
    public void FormatterWorksForEqualSignInEnsures() {
      FormatterWorksFor(@"
method test() {
  calc {
    mult(mult(a, b), c)(i)(j);
  == {
       forall k: Index
         ensures Sum((l: Index) => a(i)(l) * b(l)(k)) * c(k)(j)
                 ==
                 Sum((l: Index) => a(i)(l) * b(l)(k) * c(k)(j))
       {
       }
     }
    Sum((k: Index) => Sum((l: Index) => a(i)(l) * b(l)(k) * c(k)(j)));
  }
}
");
    }

    [Fact]
    public void FormatterWorksForUtf8InComment() {
      FormatterWorksFor(@"
//  x ∈ a[..3] Dafny won’t prove, Wüstholz would, Mikaël doesn’t voilà Great job 
const x: int
");
    }

    [Fact]
    public void FormatterWorksForControlFlow() {
      FormatterWorksFor(@"
method ControlFlowTest() {
  while
    decreases O - k;
  {
    case k < O && k % 2 == 0 =>
      d := 187; break;
    case k < O =>
      if (*) { e := 4; break InnerHasLabel; }
      if (*) { e := 7; break; }
      if (*) { e := 37; break break break; }
      k := k + 1;
  }
}
");
    }

    [Fact]
    public void FormatterWorksForLinearFunctionBody() {
      FormatterWorksFor(@"
function test(): int {
  :- Need(u);
  :- Need(u);
  :- Need(u);
  var u := u as C.UnaryOpExpr;
  x
}
");
    }

    [Fact]
    public void FormatterWorksForComparisons() {
      FormatterWorksFor(@"
function f(x: int): (y: int)
  ensures x
       == y
  ensures x
        < y
  ensures x
       <= y
  ensures x
        > y
  ensures x
       >= y
  ensures x
       != y
  ensures x
     <==> y
{ 1 }
");
    }

    [Fact]
    public void FormatterWorksForTutorialStyle() {
      FormatterWorksFor(@"
/// Tutorial style

abstract module C {

/// Now we want this

  const x := 1

/// And then that
 
  const y := 2
}
");
    }

    [Fact]
    public void FormatterWorksForForallExpressions() {
      FormatterWorksFor(@"
predicate GoodIdentifier(s: string) {
  && s != []
  && (|| 'a' <= s[0] <= 'z'
      || 'A' <= s[0] <= 'Z')
  && forall i :: 1 <= i < |s| ==>
                   || 'a' <= s[i] <= 'z'
                   || 'A' <= s[i] <= 'Z'
                   || '0' <= s[i] <= '9'
}
predicate BadIdentifier(s: string) {
  forall e, e' ::
    && Exprs.ConstructorsMatch(e, e')
    && s == """"
}
");
    }

    [Fact]
    public void FormatterWorksForIfInLemma() {
      FormatterWorksFor(@"
lemma AlltokenSpec(i: int)
  requires Valid()
  decreases |allTokens|
  requires 0 <= i < |allTokens|
  ensures allTokens == allTokens[..i] + allTokens[i].allTokens
{
  if i == 0 {
  } else {
    this.Next.AlltokenSpec(i - 1);
  }
}
");
    }

    [Fact]
    public void FormatterWorksForNestedIfElse() {
      var testCase = @"
function test(): int {
  if a then
    b
  else if c then
    d
  else
    e
}
";
      FormatterWorksFor(testCase, testCase);
    }

    [Fact]
    public void FormatterWorksForNestedConstructors() {
      FormatterWorksFor(@"
function test(): int {
  assert X;
  Some(Result(
         data[0],
         data[1])
  )
}
");
    }

    [Fact]
    public void FormatterWorksForParticularCase() {
      FormatterWorksFor(@"
module Test {
  lemma ProveMeThis(i: nat)
  {
    if i == 0 {
    } else if condition || TestIf(
                             a,
                             b,
                             c
                           ) {
      assert false;
    }
  }
  lemma ProveMeThis(i: nat)
  {
    if i == 0 {
    } else if
      condition ||
      TestIf(
        a,
        b,
        c
      ) {
      assert false;
    }
  }
}
");
    }

    [Fact]
    public void FormatterWorksForEqualPlus() {
      FormatterWorksFor(@"
function test(a: int, b: int, c: int): int 
  requires a == b + d + e +
                f + g + h
{ 1 }
");
    }

    [Fact]
    public void FormatterWorksForCommentBeforeElse() {
      FormatterWorksFor(@"
function test(i: int): int {
  if true then
    Class.StaticMethod(argument)
  // Otherwise, we are good.
  else
    0
}
");
    }

    [Fact]
    public void FormatterWorksForElseWithComplexContent() {
      FormatterWorksFor(@"
function Test(value: string): bool {
  if value == """" then Constructor(arg)
  else if value == ""1"" then Constructor1(arg)
  else match Search(value) {
         case None => Constructor(1)
         case Some(ctxVal) => None
       }
}
");
    }

    [Fact]
    public void FormatterWorksForAligningHints() {
      FormatterWorksFor(@"
method Test(x: int, y: int)
  requires xy: x > 0
  requires y0: y == 0
{
  calc {
    x + 1 - y > -2;
  ==   // Reordering terms
    x > y - 3;
  <==  { assert 3 > 0; }
    x > y;
  <==> { reveal y0; }
    x > 0;
       { reveal xy; }
    true;
  }
}
");
    }

    [Fact]
    public void FormatterWorksForAlignedAmpVar() {
      FormatterWorksFor(@"
method Test()
  ensures
    && P()
    && var x := 7;
    && var y := x;
    && F(x, y)
{
}
function Align(longVariableName: bool): int
{
  longVariableName &&
  var x2 := LongModuleName.LongStaticMethodName(longVariableName);
  match A
  {
    case _ => 1
  }
}
");
    }

    [Fact]
    public void FormatterWorksForDoublecomment() {
      FormatterWorksFor(@"
datatype Test =
  | Zero
    /* Zero */
  | One
    // One
  | MOne /* -1 */
    // Minus one
  | Both /* 2 */
    /* Two */
");
    }

    [Fact]
    public void FormatterWorksForEqualityOnItsOwnLine() {
      FormatterWorksFor(@"
function Test(): int {
  if A then
    assert C(a1, b1, c1)
         < D(a2, b2, c2);
    assert (C(a1, b1, c1)
            < D(a2, b2, c2));
    assert (  C(a1, b1, c1)
            < D(a2, b2, c2));
    assert A
           && C(a1, b1, c1)
            < D(a2, b2, c2);
    assert A
           && C(a1, b1, c1)
              == D(a2, b2, c2);
    assert A
           &&    C(a1, b1, c1)
              == D(a2, b2, c2);
    ( C(a1, b1, c1)
      < D(a2, b2, c2) )
  else
    C(a1, b1, c1)
    == D(a2, b2, c2)
}");
    }

    [Fact]
    public void FormatterWorksForObjectCreation() {
      FormatterWorksFor(@"
method Test() {
  var g := new ClassName.ConstructorName(
    argument1,
    argument2,
    argument3
  );
  var g := Datatype.ConstructorName(
    argumenta,
    argumentb,
    argumentc
  );
  :- Module.Need(
    arg1,
    arg2
  );

  var g :=
    Datatype.ConstructorName(
      argumentd,
      argumente,
      argumentf
    );
  var h :=
    new ClassName.ConstructorName2(
      argument4,
      argument5,
      argument6
    );
}
", reduceBlockiness: true);
      FormatterWorksFor(@"
method Test() {
  var g := new ClassName.ConstructorName(
             argument1,
             argument2,
             argument3
           );
  var g := Datatype.ConstructorName(
             argumenta,
             argumentb,
             argumentc
           );
  :- Module.Need(
       arg3,
       arg4
     );

  var g :=
    Datatype.ConstructorName(
      argumentd,
      argumente,
      argumentf
    );
  var h :=
    new ClassName.ConstructorName2(
      argument4,
      argument5,
      argument6
    );
}
", reduceBlockiness: false);
    }

    [Fact]
    public void FormatterWorksForSingleDatatypeConstructor() {
      FormatterWorksFor(@"
datatype C = C(
  arg1: int,
  arg2: int
)
", reduceBlockiness: true);
      FormatterWorksFor(@"
datatype C = C(
               arg1: int,
               arg2: int
             )
", reduceBlockiness: false);
    }

    [Fact]
    public void FormatterWorksForUsualMatchCasePatterns() {
      FormatterWorksFor(@"
method test() {
  var longName := match x {
    case 1 => Hello(
      arg1,
      arg2
    )
    case 2 => match z {
      case 1 => b 
      case 2 => c
    }
  };
  match x {
    case 1 => Bring(
      [ 1
      , 2]
    );
  }
}
", reduceBlockiness: true);
      FormatterWorksFor(@"
method test() {
  var longName := match x {
                    case 1 => World(
                                arg3,
                                arg4
                              )
                    case 2 => match z {
                                case 1 => b 
                                case 2 => c
                              }
                  };
  match x {
    case 1 => Bring(
                [ 1
                , 2]
              );
  }
}
", reduceBlockiness: false);
    }

    [Fact]
    public void FormatterWorksForClassExtend() {
      FormatterWorksFor(@"
class A
  extends B<
    C<
      E
    >,
    D
  > {
}

class V
  extends 
    A,
    B
  , C {
}

class W extends 
  AA,
  BB
, CC {
}
");
    }

    [Fact]
    public void FormatterWorksForSetComprehension() {
      FormatterWorksFor(@"
function test(): int {
  | set i: nat
      | i < 10
    :: i |
}
");
    }

    [Fact]
    public void FormatterWorksForMatchInMap() {
      FormatterWorksFor(@"
method AlignMapComplex(a: int) returns (r: map<string, string>) {
  return ComputeMap(map[
                      ""a"" := Compute(
                        match a {
                          case 0 => ""Zero""
                          case _ => ""NonZero""
                        })]);
}
");
    }

    [Fact]
    public void FormatterWorksForAbstractModuleDecl() {
      FormatterWorksFor(@"
abstract module C {
  export Body provides AF reveals g
 
  import AF : A`Spec
}
");
    }

    [Fact]
    public void FormatterWorksForCommentsHoldingTogether() {
      FormatterWorksFor(@"
   const x := 2;     /* start of comment
  These words aligned:  start */

const y := 3;", @"
const x := 2;      /* start of comment
These words aligned:  start */

const y := 3;");

      FormatterWorksFor(@"
const x := 4;
    /* start of comment
  end of comment
 should stay aligned*/
const y := 5;", @"
const x := 4;
   /* start of comment
 end of comment
should stay aligned*/
const y := 5;");

      FormatterWorksFor(@"
const x := 6;

    /* start of comment
  end of comment
 should stay aligned*/
const y := 7;", @"
const x := 6;

   /* start of comment
 end of comment
should stay aligned*/
const y := 7;");
    }


    [Fact]
    public void FormatterWorksForMultilineCommentsStartingWithRowOfStars() {
      FormatterWorksFor(@"
/***********
 * These are test cases for monotonicity of the the _k parameter.  However, monotonicity
 * does not appear to be useful in the test suite, and it is possible that the axioms
 * about monotonicity are expensive performance-wise.  Therefore, the monotonicity axioms
 * are currently not produced--they are controled by #if WILLING_TO_TAKE_THE_PERFORMANCE_HIT.
 ***********/
function test(): int
");
    }

    [Fact]
    public void FormatterWorksForChainingEquality() {
      FormatterWorksFor(@"

lemma SeventeenIsNotEven()
  ensures !Even(N(17))
{
  assert Even(N(17))
      == Even(N(15)) ==
         Even(N(13)) ==
         Even(N(11))
      == 
         Even(N(9))
      == Even(N(7))
      == Even(N(5))
       < Even(N(3))
      == Even(N(1))
      == false;
}
");
    }

    [Fact]
    public void FormatterWorksForAligningThenAndElseIfAligned() {
      var testCase = @"
predicate Valid()
{
  data.Length == N &&
  (N == 0 ==> len == start == 0 && Contents == []) &&
  (N != 0 ==> len <= N && start < N) &&
  Contents == if start + len <= N then data[start..start+len]
                                  else data[start..] + data[..start+len-N]
}
";
      FormatterWorksFor(testCase, testCase);
    }

    [Fact]
    public void FormatterWorksForConsecutiveComments() {
      var testCase = @"
abstract module M0 {
  /******* State *******/
  type State(!new)
  function DomSt(st: State): set<Path>
  function GetSt(p: Path, st: State): Artifact
    requires p in DomSt(st);

  // cached part of state
  type HashValue
  function DomC(st: State): set<HashValue>
  function Hash(p: Path): HashValue
  /* Note, in this version of the formalization and proof, we only record which things are in the
     cache.  The actual cache values can be retrieved from the system state.
  type Cmd
  function GetC(h: HashValue, st: State): Cmd
  */
  function UpdateC(cmd: string, deps: set<Path>, exps: set<string>, st: State): State

  /******* Semantics *******/

  /******* Function 'build' *******/
  function build(prog: Program, st: State, useCache: bool): Tuple<Expression, State>
    requires Legal(prog.stmts);
  {
    do(prog.stmts, st, EmptyEnv(), useCache)
  }
}
";
      FormatterWorksFor(testCase, testCase);
    }

    [Fact]
    public void FormatterWorksForCommentsOfCases() {
      FormatterWorksFor(@"
datatype Dt =
  | Int(int)
  // | ISet(iset<Dt>) //  This definition is not allowed because Dt appears in a non-strict/lax position
  // | IMap0(imap<Dt,int>) //  This definition is not allowed because Dt appears in a non-strict/lax position
  | IMap1(imap<int,Dt>)
  // | Last case commented out

method M4() {
  if {
    case true => even := noll as EvenInt;
    //case true => even := b67 as EvenInt;  // error: bv67 may be odd  // disabled because it doesn't terminate with 4.4.2 Z3
    case b67 as int % 2 == 0 => even := b67 as EvenInt;
    // case false => // Let's forget about this case
  }
}");
    }

    [Fact]
    public void FormatterWorksForSeqSetMapDisplay() {
      FormatterWorksFor(@"
function method AlignSeq(): seq<seq<int>> {
  [ [ 1, 2, 3 ],
    [ 4,
      5
    , 6 ]
  , [ 7, 8, 9 ] ]
}

function method AlignMap(): map<int, int> {
  map[ 1 := 2,
       2 := 3
     , 4 := 5
     , 6 :=
         7
     , 8
       := 9 ]
}

function method AlignSet(): set<int> {
  { 1,
    2
  , 3} + {
    1,
    2
  , 3
  }
}
");
    }

    [Fact]
    public void FormatterWorksForNewtypeWithMember() {
      FormatterWorksFor(@"
newtype Even = x : int | x % 2 == 0
{
  method {:timeLimitMultiplier 4} NewtypeTest(y:int) {
    assert y == y;
  }
}

type Opaque<
    Y>
{
  static const Static: Y
  const Instance: Y
}
");
    }

    [Fact]
    public void FormatterWorksForAdvancedClosures() {
      FormatterWorksFor(@"
function method Compose<A,B,C>(f: B ~> C, g:A ~> B): A ~> C
{
  x reads g.reads(x)
    reads if g.requires(x) then f.reads(g(x)) else {}
    requires g.requires(x)
    requires g.requires(x)
    requires f.requires(g(x))
  => f(g(x))
}

function method Twice<A>(f : A ~> A): A ~> A
{
  x requires f.requires(x) && f.requires(f(x))
    reads f.reads(x), if f.requires(x) then f.reads(f(x)) else {}
  => f(f(x))
}

function method Apply'<A,B>(f: A ~> B) : A ~> B
{
  x reads f.reads(x)
    requires f.requires(x)
  => f(x)
}

method LRead() {
  var o : object?;
  var f : Ref<() ~> bool>;
  f := new Ref<() ~> bool>;
  f.val := () reads f
              reads f.val.reads()
              reads if o in f.val.reads() then {} else {o}
           => true;
}

function method TreeMapZ<A,B>(t0: Tree<A>, f: A ~> B): Tree<B>
  requires PreZ(f, TreeData(t0))
  reads PreZ.reads(f, TreeData(t0))
  decreases t0
{
  var Branch(x, ts) := t0;
  var g := t requires t in ListData(ts) && PreZ(f, TreeData(t))
             reads set x, y | x in TreeData(t) && y in f.reads(x) :: y
           => TreeMapZ(t, f);
  Branch(f(x), MapZ(ts, g))
}
");
    }

    [Fact]
    public void FormatterWorksForExtremePredicates() {
      FormatterWorksFor(@"
lemma Lemma(k: ORDINAL, r: real)
  requires E.P(r)
  requires E.P#[k](r)
{}");
    }

    [Fact]
    public void FormatterWorksForCommentAfterSubsetType() {
      FormatterWorksFor(@"
module R1 refines Q {
  type G = real  // specify G
  // now, it is known how to initialize
}");
    }

    [Fact]
    public void FormatterWorksForCalcStatements() {
      FormatterWorksFor(@"
lemma Test() {
  calc {
    1;
  ==#[k]
    1;
  ==#[k]
    1;
  }
  calc {
     1;
  <  3;
  == 4;
  }
  calc {
     5;
  == 2;
  >= 7;
  >  8;
  }
  calc {
    10;
  ==
    calc {
      10;
    ==
      10;
    }
    10;
  <=
    calc {
       10;
    <= 20;
    }
    20;
  < calc {
      20;
    < 30;
    }
    30;
  }
  calc {
         1;
  ==#[k] 1+0;
  ==#[k] 0+1;
  }
  calc {
       false;
  ==>  true;
  <==> 1 == 1;
  }
  calc {
    false;
  ==>
    true;
  <==>
    1 == 1;
  }
  calc {
      false;
  ==> true;
  ==> true;
  }

  calc {
    false;
  ==>
    true;
  ==>
    true;
  }
  calc {
       true;
  <==  false;
  <==> 1 == 0;
  }
  calc {
    A;
    O[j..] + O[..j];
    O[j..j+1] + O[j+1..] + O[..j];
    O[j..j+1] + (O[j+1..] + O[..j]);
  }
  calc {
    C;
    A[1..] + [A[0]];
    { assert A[0] == O[j] && A[1..] == O[j+1..] + O[..j]; }
    O[j+1..] + O[..j] + [O[j]];
    // Pre comment
    {
      // Begin comment
      assert [O[j]] == O[j..j+1];
      // Inside comment
    }
    // Extra comment
    O[j+1..] + O[..j] + O[j..j+1];
    O[j+1..] + (O[..j] + O[j..j+1]);
    { assert O[..j] + O[j..j+1] == O[..j+1]; }
    O[j+1..] + O[..j+1];
  }
}");
    }


    [Fact]
    public void FormatterWorksForCalcAndIfElseNonNested() {
      FormatterWorksFor(@"
function test(i: nat): nat {
  if i == 0 then 0 else
  if i == 1 then 1 else
  test(i - 1) + test(i - 2)
}

lemma test2() {
  calc {
      A;
  ==> B;
  ==> { Lemma(); }
      C;
  ==> // IsPrime_Alt
      D;
      E;
  }
  calc {
    product(s);
    x * y * product(s - {x} - {y});
    /* TODO
     */
    // TODO
    { assert y == PickLargest(s - {x}); }
    x * product(s - {x});
  }
  calc {
    A;
    B;
  ==> { Lemma(); }
    C;
  ==> // IsPrime_Alt
    D;
    E;
  }
}

// Last comment
");
    }

    [Fact]
    public void FormatterWorksForSmokeTest() {
      FormatterWorksFor(@"
include ""../libraries/src/Wrappers.dfy""
import opened Wrappers

method id<T>(r: T) returns (r2: T)  {
  r2 := r;
}

method test(s: string) returns (r: Option<string>) {
  r := None;
  var x :- id<Option<string>>(Some(s));
  r := Some(x);
}

method Main() {
  var x := test(""ok"");
  if x.Some? {
    print x.value;
  } else {
    print ""None?!"";
  }
}
", @"
include ""../libraries/src/Wrappers.dfy""
import opened Wrappers

method id<T>(r: T) returns (r2: T)  {
  r2 := r;
}

method test(s: string) returns (r: Option<string>) {
  r := None;
  var x :- id<Option<string>>(Some(s));
  r := Some(x);
}

method Main() {
  var x := test(""ok"");
  if x.Some? {
    print x.value;
  } else {
    print ""None?!"";
  }
}
");
    }

    [Fact]
    public void FormatterWorksForLabels() {
      var test = @"
method BreakLabels(s: seq<int>)
  requires |s| == 1000
{
  label A:
  for i := 0 to 100
  {
    label B:
    label C:
    for j := 100 downto 0
    {
    }
  }
}
method Test() {
  var a, b, c, d, e;
  var i := 0;
  while (i < M)
  {
    var j := 0;
    label InnerHasLabel:
    while (j < N)
    {
    }
  }
  label a:
  while {
    case true =>
      for k := 0 to 10
        invariant k <= 5
      {
        if k == 5 {
          break break;
        }
        c := c + 1;
      }
  }
  var i := 0;
  while i == 1
    decreases
      10 - i,
      1
      , 2
  {
  }
  while
    decreases
      310 - i,
      31
      , 32
  {
  }
  label Loop:
  while
    decreases 11 - i,
              12
            , 23
  {
    case i < 10 =>
      if i == 929 {
      } else if i < 7 {
        i := i + 1;
        continue Loop;
      } else {
        b := true;
        break Loop;
      }
      assert false; // unreachable
      expect false; // unreachable
  }
}
";
      FormatterWorksFor(test, test);
    }

    private void FormatterWorksFor(string testCase, string expectedProgramString = null, bool expectNoToken = false, bool reduceBlockiness = true) {
      BatchErrorReporter reporter = new BatchErrorReporter();
      var options = DafnyOptions.Create();
      DafnyOptions.Install(options);
      var newlineTypes = Enum.GetValues(typeof(Newlines));
      foreach (Newlines newLinesType in newlineTypes) {
        currentNewlines = newLinesType;
        // This formatting test will remove all the spaces at the beginning of the line
        // and then recompute it. The result should be the same string.
        var programString = AdjustNewlines(testCase);
        var programNotIndented = expectedProgramString != null ? programString : indentRegex.Replace(programString, "");
        var expectedProgram = expectedProgramString != null ? AdjustNewlines(expectedProgramString) : removeTrailingNewlineRegex.Replace(programString, "");

        ModuleDecl module = new LiteralModuleDecl(new DefaultModuleDecl(), null);
        Microsoft.Dafny.Type.ResetScopes();
        BuiltIns builtIns = new BuiltIns();
        Parser.Parse(programNotIndented, "virtual", "virtual", module, builtIns, reporter);
        var dafnyProgram = new Program("programName", module, builtIns, reporter);
        if (reporter.ErrorCount > 0) {
          var error = reporter.AllMessages[ErrorLevel.Error][0];
          Assert.False(true, $"{error.message}: line {error.token.line} col {error.token.col}");
        }

        var firstToken = dafnyProgram.GetFirstTopLevelToken();
        if (firstToken == null && !expectNoToken) {
          Assert.False(true, "Did not find a first token");
        }

        //TODO(Mikael) Make sure every token is owned.
        //EnsureEveryTokenIsOwned(programNotIndented, dafnyProgram);
        var reprinted = firstToken != null && firstToken.line > 0 ?
          Formatting.__default.ReindentProgramFromFirstToken(firstToken, IndentationFormatter.ForProgram(dafnyProgram, reduceBlockiness))
          : programString;
        if (expectedProgram != reprinted) {
          Console.Write("Double formatting is not stable:\n");
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
        firstToken = dafnyProgram.GetFirstTopLevelToken();
        var reprinted2 = firstToken != null && firstToken.line > 0 ? Formatting.__default.ReindentProgramFromFirstToken(firstToken,
          IndentationFormatter.ForProgram(dafnyProgram, reduceBlockiness)) : reprinted;
        Assert.Equal(reprinted, reprinted2);
      }
    }

    private void EnsureEveryTokenIsOwned(string programNotIndented, Program dafnyProgram) {
      var firstToken = dafnyProgram.GetFirstTopLevelToken();
      if (firstToken == null) {
        return;
      }
      // Step 1: Collect all the tokens of the program
      var tokensWithoutOwner = new HashSet<int>();
      var posToOwnerNode = new Dictionary<int, List<INode>>();

      var t = firstToken;
      while (t != null) {
        if (t.val != "") {
          tokensWithoutOwner.Add(t.pos);
        }

        t = t.Next;
      }

      void ProcessOwnedTokens(INode node) {
        var ownedTokens = node.OwnedTokens;
        foreach (var token in ownedTokens) {
          tokensWithoutOwner.Remove(token.pos);
          posToOwnerNode.GetOrCreate(token.pos, () => new List<INode>()).Add(node);
        }
      }

      void ProcessNode(INode node) {
        if (node == null) {
          return;
        }
        ProcessOwnedTokens(node);
        foreach (var child in node.ConcreteChildren) {
          ProcessNode(child);
        }
      }
      ProcessNode(dafnyProgram);

      // Step 3: Report any token that was not removed
      if (tokensWithoutOwner.Count > 0) {
        IToken? notOwnedToken = firstToken;
        while (notOwnedToken != null && !tokensWithoutOwner.Contains(notOwnedToken.pos)) {
          notOwnedToken = notOwnedToken.Next;
        }

        if (notOwnedToken == null) {
          return;
        }

        var prevOwnedToken = notOwnedToken.Prev;
        var nextOwnedToken = notOwnedToken.Next;
        while (nextOwnedToken != null && !posToOwnerNode.ContainsKey(nextOwnedToken.pos)) {
          nextOwnedToken = nextOwnedToken.Next;
        }
        var prevNodeOwning = posToOwnerNode[prevOwnedToken.pos];
        var nextNodeOwning = nextOwnedToken != null ? posToOwnerNode[nextOwnedToken.pos] : null;
        var before = programNotIndented.Substring(0, notOwnedToken.pos);
        var after = programNotIndented.Substring(notOwnedToken.pos + notOwnedToken.val.Length);
        var beforeContextLength = Math.Min(before.Length, 50);
        var wrappedToken = "[[[" + notOwnedToken.val + "]]]";
        var errorString = before.Substring(before.Length - beforeContextLength) + wrappedToken + after;
        errorString = errorString.Substring(0,
          Math.Min(errorString.Length, beforeContextLength + wrappedToken.Length + 50));

        Assert.False(true, $"The token '{notOwnedToken.val}' (L" + notOwnedToken.line + ", C" + (notOwnedToken.col + 1) + ") or (P" + notOwnedToken.pos + ") is not owned:\n" +
                           errorString
                           );
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
