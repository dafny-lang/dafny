using JetBrains.Annotations;
using Xunit;
using Xunit.Abstractions;

namespace DafnyPipeline.Test;

[Collection("Singleton Test Collection - FormatterForSpecifications")]
public class FormatterForSpecifications : FormatterBaseTest {
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
  public void FormatterWorksForAssertAssumeExpectPrintReveal() {
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
}
// Trailing comments
");
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


  public FormatterForSpecifications([NotNull] ITestOutputHelper output) : base(output)
  {
  }
}
