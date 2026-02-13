// RUN: %testDafnyForEachResolver --expect-exit-code 4 "%s"


lemma M(n: nat) //returns (y: nat)
{
  var y := F(n, 0);
}
ghost function F(n: nat, p: int): nat
{
  calc {
    100;
  <  { if n != 0 { M(n-1); } }
    102;
  }
  n
}

lemma MM(n: nat) returns (y: nat)
  decreases n, 0
{
  if n != 0 {
    y := FF(n-1);
  } else { y := *; }
}
ghost function FF(n: nat): nat
  decreases n, 1
{
  calc {
    100;
  <  { var y := MM(n); }
    102;
  }
  n
}

lemma P(n: nat)
{
  if n != 0 {
    var y :=
      calc {
        12;
        { P(n-1); }
        12;
      }
      100;
    assert y == 100;
  }
}
lemma Q(n: nat)
{
  if n != 0 {
    var y :=
      calc {
        12;
        { Q(n+1); }  // error: cannot prove termination
        12;
      }
      100;
    assert y == 102;  // error: assertion does not hold
  }
}

// ---------------------

ghost function Fact(n: nat): nat
{
  if n == 0 then 1 else n * Fact(n-1)
}

lemma L(n: nat)
  ensures 1 <= Fact(n)
{
}

ghost function F_Fails(n: nat): int
{
  50 / Fact(n)  // error: possible division by zero
}

ghost function F_Succeeds(n: nat): int
{
  L(n);
  50 / Fact(n)
}

ghost function F_PreconditionViolation(n: int): int
{
  L(n);  // error: argument might be negative
  50 / Fact(n)
}

// --------------------- These had had parsing problems in the past

lemma MyLemma(x: int) {
  var d: Dtz := *;
  if 0 < x {
    var y: int := *;
    match MyLemma(y); d {  // error: cannot prove termination
      case Cons0(_) =>
      case Cons1(_) =>
    }
  }
}

ghost function Parsing_Regression_test0(): int
{
  var x := 12;
  assert x < 20;
  MyLemma(x);
  calc { x; < x+1; }
  // and again
  var x := 12;
  assert x < 20;
  MyLemma(x);
  calc { x; < x+1; }
  17
}

datatype Dtz = Cons0(int) | Cons1(bool)

ghost function Parsing_Regression_test1(dtz: Dtz): int
{
  match dtz
  case Cons0(s) =>
    var x := 12;
    assert x < 20;
    MyLemma(x);
    calc { x; < x+1; }
    // and again
    var x := 12;
    assert x < 20;
    MyLemma(x);
    calc { x; < x+1; }
    17
  case Cons1(_) =>
    var x := 12;
    assert x < 20;
    MyLemma(x);
    calc { x; < x+1; }
    // and again
    var x := 12;
    assert x < 20;
    MyLemma(x);
    calc { x; < x+1; }
    19
}

ghost function Parsing_Regression_test2(): int
{
  // parentheses should be allowed anywhere
  var x := 12;
  ( assert x < 20;
    ( MyLemma(x);
      ( calc { x; < x+1; }
        ( var x := 12;
          ( assert x < 20;
            ( MyLemma(x);
              ( calc { x; < x+1; }
                17
  ) ) ) ) ) ) )
}

function PartialToTheDiagonal(x: int, y: int): int
  requires x == y
{
  5
}

opaque function GimmieSeven(i: int): int { 7 }
lemma AboutGimmieSeven(i: int)
  ensures GimmieSeven(i) == 7
{
  reveal GimmieSeven();
}

function TestForallStatement0(a: int, b: int): int
{
  PartialToTheDiagonal(GimmieSeven(a), GimmieSeven(b)) // error: precondition violation
}

function TestForallStatement1(a: int, b: int): int
{
  reveal GimmieSeven();
  PartialToTheDiagonal(GimmieSeven(a), GimmieSeven(b))
}

function TestForallStatement2(a: int, b: int): int
{
  AboutGimmieSeven(a);
  AboutGimmieSeven(b);
  PartialToTheDiagonal(GimmieSeven(a), GimmieSeven(b))
}

function TestForallStatement3(a: int, b: int): int
{
  assert GimmieSeven(a) == GimmieSeven(b) by {
    forall i
      ensures GimmieSeven(i) == 7
    {
      AboutGimmieSeven(i);
    }
  }
  PartialToTheDiagonal(GimmieSeven(a), GimmieSeven(b))
}

function TestForallStatement4(a: int, b: int): int
{
  assert forall i :: GimmieSeven(i) == 7 by {
    forall i
      ensures GimmieSeven(i) == 7
    {
      AboutGimmieSeven(i);
    }
  }
  PartialToTheDiagonal(GimmieSeven(a), GimmieSeven(b))
}

function TestForallStatement5(a: int, b: int): int
{
  forall i
    ensures GimmieSeven(i) == 7
  {
    AboutGimmieSeven(i);
  }
  PartialToTheDiagonal(GimmieSeven(a), GimmieSeven(b))
}

function TestForallStatement6(a: int, b: int): int
{
  forall i {
    AboutGimmieSeven(i);
  }
  PartialToTheDiagonal(GimmieSeven(a), GimmieSeven(b))
}

function TestForallStatement7(a: int, b: int): int
  requires 0 <= a && 0 <= b
{
  forall i | 0 <= i
    ensures GimmieSeven(i) == 7
  {
    AboutGimmieSeven(i);
  }
  PartialToTheDiagonal(GimmieSeven(a), GimmieSeven(b))
}

function TestForallStatement8(a: int, b: int): int
  requires 0 <= a && 0 <= b
{
  forall i | 0 <= i {
    AboutGimmieSeven(i);
  }
  PartialToTheDiagonal(GimmieSeven(a), GimmieSeven(b))
}
