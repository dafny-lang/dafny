// RUN: %exits-with 4 %verify --show-hints --allow-warnings --rprint "%t.rprint.dfy" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// RUN: %OutputCheck --file-to-check "%t.rprint.dfy" "%s"

// The trigger generator splits these quantifiers at their conjunctions and disjunctions, but only the verifier's
// translation has the parts, so a copy that a substitution makes is the quantifier as written

// The printer prints a quantifier as its parts, and a binding guard as written, without the attributes that record the
// parts
// CHECK-NOT: _part

// The lambda's body reaches the well-formedness check through a substitution. Given the first part, which holds for
// every i, the second is well-formed, but the quantifier as written is not.
method WellFormedness(s: seq<int>, t: seq<int>)
  requires |t| == |s|
{
  var f := (k: int) => forall i | 0 <= i < |s| :: s[i] > 0 && 10 / s[(i + 1) % |s|] > t[i]; // error: division by zero
}

predicate Even(x: int) { x % 2 == 0 }
predicate Triple(x: int) { x % 3 == 0 }

// A binding guard in the lambda's body reaches the verifier through a substitution too, and the trigger generator
// splits it
method InLambda() {
  var f := (k: int) => forall n | 0 <= n < k ::
    calc { Even(2 * n); { if case x :| Triple(x) || (Even(x) && Even(x + 1)) => case true => } true; } Triple(3 * n);
}

datatype D = D(n: int)
predicate A(i: int, d: D)
predicate B(i: int)

// The existence check takes the part exists i :: B(i), which does not mention d, for a disjunct of its own, so it
// needs no value for d
method SuchThat()
  requires B(0)
{
  ghost var d: D :| exists i :: B(i) || (A(i, d) && A(i + 1, d));
}

ghost function LetSuchThat(): D
  requires B(0)
{
  var d: D :| exists i :: B(i) || (A(i, d) && A(i + 1, d)); d
}

predicate P(x: int)
function H(x: int): int

// The verifier translates each part with its own triggers
// CHECK: \(forall x: int \{:trigger P\(x\)\} ::
// CHECK-NEXT: P\(x\)\) &&
// CHECK-NEXT: forall x: int /\*\{:_trigger H\(x \+ 1\), H\(x\)\}\*/ /\*\{:_named x \+ 1\}\*/ ::
// CHECK-NOT: _part
ghost predicate Parts() {
  forall x :: P(x) && H(x) <= H(x + 1)
}

predicate Big(x: int) { x > 10 }

// The case assumes the CanCall assumption of the guard as written, which gives Big's definition at each x where P(x)
// does not hold, and not that of its parts, which gives it only if P(x) holds for no x
method Guard() {
  if
  case x :| P(x) || (Big(x) && Big(x + 1)) =>
    assert P(x) || x > 10;
  case true =>
}

function G(x: int): int

// The trigger generator joins the two parts again, as they get the same trigger, and the verifier makes the joined part
// from both
method Joined()
  requires forall x :: 0 <= G(x)
{
  assert forall x :: 0 <= G(x) && G(x) < 10; // error: assertion might not hold
}

module Callee {
  ghost predicate P(x: int)
  ghost predicate Q(x: int)

  function F(b: bool): int
    requires forall x :: P(x) ==> b
  {
    0
  }

  function K(a: bool, b: bool): int
    requires forall x :: a && (P(x) || !P(x)) && (Q(x) ==> P(x + 1)) && b
  {
    0
  }

  function E(a: bool, b: bool): int
    requires exists x :: a || (P(x) && P(x + 1)) || Q(x) || b
  {
    0
  }

  // Without its precondition, the definition gives false
  function Bad(n: int): int
    requires n > 0
  {
    if n <= 0 then Bad(n) + 1 else 0
  }
}

// {:autoReq} copies a callee's precondition into the caller's for the arguments. The verifier makes the parts of the
// copy at the positions of the conjuncts of the callee's parts, whatever conjuncts the arguments have, and the trigger
// generator does not select the copy's triggers again.
module Caller {
  import Callee

  // The part of the copy is P(x) ==> c && d
  function {:autoReq} G(c: bool, d: bool): int {
    Callee.F(c && d)
  }

  method Call(c: bool)
    requires forall x :: Callee.P(x) ==> c
  {
    var y := G(c, false); // error: precondition might not hold
  }

  // A split of the copy would drop true and split c && Bad(n) == 0 in two, so its conjuncts are not where K's are, and
  // the CanCall assumption of parts made from it would give Bad's definition where c does not hold, and so false
  function {:autoReq} H(c: bool, n: int): int {
    Callee.K(true, c && Callee.Bad(n) == 0)
  }

  method CallH()
    requires forall x :: Callee.Q(x) ==> Callee.P(x + 1)
    ensures false
  {
    var y := H(false, 0); // error: precondition might not hold
  }

  // A split of the copy would drop false and split c || d in two
  function {:autoReq} I(c: bool, d: bool): int {
    Callee.E(false, c || d)
  }

  method CallI()
    requires Callee.Q(3)
  {
    var y := I(false, false);
  }
}
