// RUN: %dafny /compile:3 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Rustan Leino
// 13 April 2015, and many subsequent enhancements and revisions
// VerifyThis 2015
// Problem 2 -- Parallel GCD

method SequentialGcd(A: int, B: int) returns (gcd: int)
  requires A > 0 && B > 0
  ensures gcd == Gcd(A, B)
{
  var a, b := A, B;
  while
    invariant 0 < a && 0 < b
    invariant Gcd(A, B) == Gcd(a, b)
    decreases a + b
  {
    case a > b =>
      GcdDecrease(a, b);
      a := a - b;
    case b > a =>
      calc {
        Gcd(a, b);
        { Symmetry(a, b); }
        Gcd(b, a);
        { GcdDecrease(b, a); }
        Gcd(b - a, a);
        { Symmetry(b - a, a); }
        Gcd(a, b - a);
      }
      b := b - a;
  }
  GcdEqual(a);
  return a;
}

method ParallelGcd_ReadAB_WithoutTermination(A: int, B: int) returns (gcd: int)
  requires A > 0 && B > 0
  ensures gcd == Gcd(A, B)
  decreases *
{
  var a, b := A, B;
  var pc0, pc1 := 0, 0;  // program counter for the two processes
  var a0, b0, a1, b1;  // local variables for the two processes
  while !(pc0 == 2 && pc1 == 2)
    invariant 0 < a && 0 < b
    invariant Gcd(A, B) == Gcd(a, b)
    invariant 0 <= pc0 < 3 && 0 <= pc1 < 3
    invariant pc0 == 1 && b0 <= a0 ==> a0 == a && b0 == b
    invariant pc1 == 1 && a1 <= b1 ==> a1 == a && b1 == b
    invariant (pc0 == 2 ==> a == b) && (pc1 == 2 ==> a == b)
    decreases *
  {
    if {
      case pc0 == 0              => a0, b0, pc0 := a, b, 1;
      case pc0 == 1 && b0 < a0   => GcdDecrease(a, b);
                                    a, pc0 := a0 - b0, 0;
      case pc0 == 1 && b0 > a0  => pc0 := 0;
      case pc0 == 1 && b0 == a0 => pc0 := 2;  // move into a halting state
      case pc1 == 0             => a1, b1, pc1 := a, b, 1;
      case pc1 == 1 && a1 < b1  => Symmetry(a, b); GcdDecrease(b, a); Symmetry(b - a, a);
                                   b, pc1 := b1 - a1, 0;
      case pc1 == 1 && a1 > b1  => pc1 := 0;
      case pc1 == 1 && a1 == b1 => pc1 := 2;  // move into a halting state
    }
  }
  GcdEqual(a);
  gcd := a;
}

method ParallelGcd_WithoutTermination(A: int, B: int) returns (gcd: int)
  requires A > 0 && B > 0
  ensures gcd == Gcd(A, B)
  decreases *
{
  var a, b := A, B;
  var pc0, pc1 := 0, 0;  // program counter for the two processes
  var a0, b0, a1, b1;  // local variables for the two processes
  while !(pc0 == 3 && pc1 == 3)
    invariant 0 < a && 0 < b
    invariant Gcd(A, B) == Gcd(a, b)
    invariant 0 <= pc0 < 4 && 0 <= pc1 < 4
    invariant (pc0 == 0 || a0 == a) && (pc1 == 0 || b1 == b)
    invariant pc0 == 2 ==> b <= b0 && (b0 <= a0 ==> b0 == b)
    invariant pc1 == 2 ==> a <= a1 && (a1 <= b1 ==> a1 == a)
    invariant (pc0 == 3 ==> a == b) && (pc1 == 3 ==> a == b)
    decreases *
  {
    if {
      case pc0 == 0             => a0, pc0 := a, 1;
      case pc0 == 1             => b0, pc0 := b, 2;
      case pc0 == 2 && a0 > b0  => GcdDecrease(a, b);
                                   a, pc0 := a0 - b0, 0;
      case pc0 == 2 && a0 < b0  => pc0 := 0;
      case pc0 == 2 && a0 == b0 => pc0 := 3;
      case pc1 == 0             => b1, pc1 := b, 1;
      case pc1 == 1             => a1, pc1 := a, 2;
      case pc1 == 2 && b1 > a1  => Symmetry(a, b); GcdDecrease(b, a); Symmetry(b - a, a);
                                   b, pc1 := b1 - a1, 0;
      case pc1 == 2 && b1 < a1  => pc1 := 0;
      case pc1 == 2 && b1 == a1 => pc1 := 3;
    }
  }
  GcdEqual(a);
  gcd := a;
}

method ParallelGcd(A: int, B: int) returns (gcd: int)
  requires A > 0 && B > 0
  ensures gcd == Gcd(A, B)
{
  var a, b := A, B;
  var pc0, pc1 := 0, 0;  // program counter for the two processes
  var a0, b0, a1, b1;  // local variables for the two processes
  // To model fairness of scheduling, these "budget" variable give a bound on the number of times the
  // scheduler will repeatedly schedule one process to execute its "compare a and b" test.  When a
  // process executes its comparison, its budget is decreased and the budget for the other process
  // is set to some arbitrary positive amount.
  var budget0, budget1 :| budget0 > 0 && budget1 > 0;
  while !(pc0 == 3 && pc1 == 3)
    invariant 0 < a && 0 < b
    invariant Gcd(A, B) == Gcd(a, b)
    invariant 0 <= pc0 < 4 && 0 <= pc1 < 4
    invariant (pc0 == 0 || a0 == a) && (pc1 == 0 || b1 == b)
    invariant pc0 == 2 ==> b <= b0 && (b0 <= a0 ==> b0 == b)
    invariant pc1 == 2 ==> a <= a1 && (a1 <= b1 ==> a1 == a)
    invariant (pc0 == 3 ==> a == b) && (pc1 == 3 ==> a == b)
    invariant 0 <= budget0 && 0 <= budget1 && (pc0 == 3 || pc1 == 3 || 1 <= budget0 + budget1)
    // With the budgets, the program is guaranteed to terminate, as is proved by the following termination
    // metric (which is a lexicographic tuple):
    decreases a + b,
              FinalStretch(pc0, pc1, a0, b0, b) + FinalStretch(pc1, pc0, b1, a1, a),
              (if pc0 == 2 && a0 < b0 && !(a < b) then 1 else 0) + (if pc1 == 2 && b1 < a1 && !(b < a) then 1 else 0),
              (if a < b then budget0 else 0) + (if b < a then budget1 else 0),
              8 - pc0 - pc1
  {
    if {
      case pc0 == 0                            => a0, pc0 := a, 1;
      case pc0 == 1                            => b0, pc0 := b, 2;
      case pc0 == 2 && (budget0 > 0 || pc1 == 3) && a0 > b0  =>
                                                  GcdDecrease(a, b);
                                                  a, pc0 := a0 - b0, 0;
                                                  budget0, budget1 := BudgetUpdate(budget0, budget1, pc1);
      case pc0 == 2 && (budget0 > 0 || pc1 == 3) && a0 < b0  =>
                                                  pc0 := 0;
                                                  budget0, budget1 := BudgetUpdate(budget0, budget1, pc1);
      case pc0 == 2 && (budget0 > 0 || pc1 == 3) && a0 == b0 =>
                                                  pc0 := 3;
                                                  budget0, budget1 := BudgetUpdate(budget0, budget1, pc1);
      case pc1 == 0                            => b1, pc1 := b, 1;
      case pc1 == 1                            => a1, pc1 := a, 2;
      case pc1 == 2 && (budget1 > 0 || pc0 == 3) && b1 > a1  =>
                                                  Symmetry(a, b); GcdDecrease(b, a); Symmetry(b - a, a);
                                                  b, pc1 := b1 - a1, 0;
                                                  budget1, budget0 := BudgetUpdate(budget1, budget0, pc0);
      case pc1 == 2 && (budget1 > 0 || pc0 == 3) && b1 < a1  =>
                                                  pc1 := 0;
                                                  budget1, budget0 := BudgetUpdate(budget1, budget0, pc0);
      case pc1 == 2 && (budget1 > 0 || pc0 == 3) && b1 == a1 =>
                                                  pc1 := 3;
                                                  budget1, budget0 := BudgetUpdate(budget1, budget0, pc0);
    }
  }
  GcdEqual(a);
  gcd := a;
}

ghost function FinalStretch(pcThis: int, pcThat: int, a0: int, b0: int, b: int): int
{
  if pcThat != 3 then 10  // we're not yet in the final stretch
  else if pcThis == 3 then 0
  else if pcThis == 2 && a0 == b0 then 1
  else if pcThis == 1 && a0 == b then 2
  else if pcThis == 0 then 3
  else if pcThis == 2 && a0 < b0 then 4
  else 5
}

method BudgetUpdate(inThis: int, inThat: int, pcThat: int) returns (outThis: int, outThat: int)
  requires pcThat == 3 || 0 < inThis
  ensures outThis == if 0 < inThis then inThis - 1 else inThis
  ensures if pcThat == 3 then outThat == inThat else outThat > 0
{
  outThis := if 0 < inThis then inThis - 1 else inThis;
  if pcThat == 3 {
    outThat := inThat;
  } else {
    outThat :| outThat > 0;
  }
}

ghost function Gcd(a: int, b: int): int
  requires a > 0 && b > 0
{
  Exists(a, b);
  var d :| DividesBoth(d, a, b) && forall m :: DividesBoth(m, a, b) ==> m <= d;
  d
}

ghost predicate DividesBoth(d: int, a: int, b: int)
  requires a > 0 && b > 0
{
  d > 0 && Divides(d, a) && Divides(d, b)
}

ghost predicate {:opaque} Divides(d: int, a: int)
  requires d > 0 && a > 0
{
  exists n :: n > 0 && MulTriple(n, d, a)
}
ghost predicate MulTriple(n: int, d: int, a: int)
  requires n > 0 && d > 0
{
  n * d == a
}

// ----- lemmas and proofs

lemma Exists(a: int, b: int)
  requires a > 0 && b > 0
  ensures exists d :: DividesBoth(d, a, b) && forall m :: DividesBoth(m, a, b) ==> m <= d;
{
  var d := ShowExists(a, b);
}

lemma ShowExists(a: int, b: int) returns (d: int)
  requires a > 0 && b > 0
  ensures DividesBoth(d, a, b) && forall m :: DividesBoth(m, a, b) ==> m <= d;
{
  assert
    exists d :: DividesBoth(d, a, b)
  by {
    OneDividesAnything(a);
    OneDividesAnything(b);
    assert Divides(1, a);
    assert Divides(1, b);
    assert DividesBoth(1, a, b);
  }
  d :| DividesBoth(d, a, b);
  DividesUpperBound(d, a);
  DividesUpperBound(d, b);
  while true
    invariant DividesBoth(d, a, b)
    invariant d <= a && d <= b
    decreases a + b - 2*d
  {
    if exists k :: DividesBoth(k, a, b) && k > d {
      var k :| DividesBoth(k, a, b) && k > d;
      d := k;
      assert Divides(d, a);
      DividesUpperBound(d, a);
      assert d <= a;
      DividesUpperBound(d, b);
      assert d <= b;
    } else {
      return;
    }
  }
}

lemma OneDividesAnything(a: int)
  requires a > 0
  ensures Divides(1, a)
{
  reveal Divides();  // here, we use the definition of Divides
  assert MulTriple(a, 1, a);
}

lemma GcdEqual(a: int)
  requires a > 0
  ensures Gcd(a, a) == a
{
  DividesIdempotent(a);
  assert Divides(a, a);
  DividesUpperBound(a, a);
  assert DividesBoth(a, a, a);

  var k := Gcd(a, a);
  assert k > 0 && DividesBoth(k, a, a);
  assert forall m :: m > 0 && DividesBoth(m, a, a) ==> m <= k;
  assert Divides(k, a);
  DividesUpperBound(k, a);
}

lemma DividesIdempotent(a: int)
  requires a > 0
  ensures Divides(a, a)
{
  reveal Divides();  // here, we use the body of function Divides
  assert MulTriple(1, a, a);
}

lemma DividesUpperBound(d: int, a: int)
  requires d > 0 && a > 0
  ensures Divides(d, a) ==> d <= a
{
  reveal Divides();  // here, we use the body of function Divides
}

lemma Symmetry(a: int, b: int)
  requires a > 0 && b > 0
  ensures Gcd(a, b) == Gcd(b, a)
{
  var k, l := Gcd(a, b), Gcd(b, a);
  assert DividesBoth(k, a, b) && forall m :: DividesBoth(m, a, b) ==> m <= k;
  assert DividesBoth(l, b, a) && forall m :: DividesBoth(m, b, a) ==> m <= l;
  assert DividesBoth(l, a, b);
  assert forall m :: DividesBoth(m, b, a) ==> m <= l && DividesBoth(m, a, b);
  assert k == l;
}

lemma GcdDecrease(a: int, b: int)
  requires a > b > 0
  ensures Gcd(a, b) == Gcd(a - b, b)
{
  var k := Gcd(a - b, b);
  assert DividesBoth(k, a-b, b) && forall m, mm :: mm == a - b ==> DividesBoth(m, mm, b) ==> m <= k; // WISH: auto-generate 'mm'
  var n := DividesProperty(k, a-b);
  assert n*k == a-b;
  var p := DividesProperty(k, b);
  assert p*k == b;

  assert n*k + p*k == a-b + b;
  assert (n+p)*k == a;

  MultipleDivides(n+p, k, a);
  assert Divides(k, a);
  assert DividesBoth(k, a, b);

  var l := Gcd(a, b);
  assert forall m :: DividesBoth(m, a, b) ==> m <= l;
  assert k <= l;

  var n' := DividesProperty(l, a);
  var p' := DividesProperty(l, b);
  assert n'*l == a;
  assert p'*l == b;
  assert n'*l - p'*l == a - b;
  assert (n' - p')*l == a - b;
  MultipleDivides(n' - p', l, a - b);
  assert Divides(l, a - b);
  assert DividesBoth(l, a - b, b);
  assert l <= k;

  assert k == l;
}

lemma MultipleDivides(n: int, d: int, a: int)
  requires n > 0 && d > 0 && n*d == a
  ensures Divides(d, a)
{
  reveal Divides();
  assert MulTriple(n, d, a);
}

lemma DividesProperty(d: int, a: int) returns (n: int)
  requires d > 0 && a > 0
  requires Divides(d, a)
  ensures n*d == a
{
  reveal Divides();
  n :| n > 0 && MulTriple(n, d, a);
}
