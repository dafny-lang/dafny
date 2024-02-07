// RUN: %diff "%s" "%s"










































































































































































module M {
method {:testEntry} RedundantAssumeMethod(n: int)
{
    // either one or the other assumption shouldn't be covered
    assume n > 4;
    assume n > 3;
    assert n > 1;
}

method {:testEntry} ContradictoryAssumeMethod(n: int)
{
    assume n > 0;
    assume n < 0;
    assume n == 5; // shouldn't be covered
    assert n < 10; // shouldn't be covered
}

method {:testEntry} AssumeFalseMethod(n: int)
{
    assume n == 15; // shouldn't be covered
    assume false;
    assert n < 10; // shouldn't be covered
}

// Obvious contradiction in requires clauses.
function {:testEntry} ObviouslyContradictoryRequiresFunc(x: nat): (r: nat)
  requires x > 10
  requires x < 10
  ensures r < x // only provable vacuously 
{
  assert x == 10; // contradicts both requires clauses
  x - 1 // not necessarily a valid nat
}

method {:testEntry} ObviouslyContradictoryRequiresMethod(x: nat) returns (r: nat)
  requires x > 10
  requires x < 10
  ensures r < x // only provable vacuously
{
  assert x == 10; // contradicts both requires clauses
  return x - 1; // not necessarily a valid nat
}

// Obvious redundancy in requires clauses.
function {:testEntry} ObviouslyRedundantRequiresFunc(x: nat): (r: nat)
  requires x < 10
  requires x < 100 // implied by previous requires clause
  ensures r < 11 // should cause body and first requires clause to be covered
{
  x + 1
}

method {:testEntry} ObviouslyRedundantRequiresMethod(x: nat) returns (r: nat)
  requires x < 10
  requires x < 100 // implied by previous requires clause
  ensures r < 11 // should cause body and first requires clause to be covered
{
  return x + 1;
}

// Obviously unnecessary requires clauses.
function {:testEntry} ObviouslyUnnecessaryRequiresFunc(x: nat): (r: nat)
  requires x < 10 // not required for the proof
{
  // cause at least a little proof work to be necessary, for nat bounds
  if (x > 5) then x + 2 else x + 1
}

method {:testEntry} ObviouslyUnnecessaryRequiresMethod(x: nat) returns (r: nat)
  requires x < 10 // not required for the proof
{
  // cause at least a little proof work to be necessary, for nat bounds
  if (x > 5) { return x + 2; } else { return x + 1; }
}

// Code obviously not constrained by ensures clause.
function {:testEntry} ObviouslyUnconstrainedCodeFunc(x: int): (r: (int, int))
  requires x > 10
  ensures r.0 > 10
{
  var a := x + 1; // constrained by ensures clause
  var b := x - 1; // not constrained by ensures clause 
  (a,
   b)
}

method {:testEntry} ObviouslyUnconstrainedCodeMethod(x: int) returns (r: (int, int))
  requires x > 10
  ensures r.0 > 10
{
  var a := x + 1; // constrained by ensures clause
  var b := x - 1; // not constrained by ensures clause
  return
    (a,
     b);
}

// Partial redundancy in requires clauses.
function {:testEntry} PartiallyRedundantRequiresFunc(x: nat): (r: nat)
  requires x < 100 && x < 10 // LHS implied by RHS
  ensures r < 11 // should cause body and RHS clause to be covered
{
  x + 1
}

// Partly unnecessary requires clause.
function {:testEntry} PartiallyUnnecessaryRequiresFunc(x: int): (r: nat)
  requires x < 10 && x > 0 // RHS required for proof, but not LHS
{
  // cause at least a little proof work to be necessary, for nat bounds
  if (x > 5) then x - 1 else x + 1
}


// Redundancy of one requires clause due to at least two others, with at least
// one of the three being partly in a separately-defined function.
function {:testEntry} MultiPartRedundantRequiresFunc(x: int): (r: int)
  requires x > 10
  requires x < 12
  requires x == 11 // implied by the previous two, but neither individually
  ensures r == 11
{
  x
}

method {:testEntry} MultiPartRedundantRequiresMethod(x: int) returns (r: int)
  requires x > 10
  requires x < 12
  requires x == 11 // implied by the previous two, but neither individually
  ensures r == 11
{
  return x;
}

// Contradiction between three different requires clauses, with at least one of
// the three being partly in a separately-defined function (function and
// method).
function {:testEntry} MultiPartContradictoryRequiresFunc(x: int, y: int): (r: int)
  requires x > 10
  requires x < 12
  requires y != 11 // contradicts the previous two
  ensures r == 11 // provable from first two preconditions, but shouldn't be covered
{
  x
}

method {:testEntry} MultiPartContradictoryRequiresMethod(x: int, y: int) returns (r: int)
  requires x > 10
  requires x < 12
  requires y != 11 // contradicts the previous two
  ensures r == 11 // provable from first two preconditions, but shouldn't be covered
{
  return x;
}

function {:testEntry} ContradictoryEnsuresClauseFunc(x: int): (r: int)
  requires x > 1
  ensures  r > x && r < 0

method {:testEntry} ContradictoryEnsuresClauseMethod(x: int) returns (r: int)
  requires x > 1
  ensures  r > x && r < 0

// Call function that has contradictory ensures clauses.
function {:testEntry} CallContradictoryFunctionFunc(x: int): (r: int)
  requires x > 1
  ensures r < 0
{
  // TODO: Dafny doesn't generate sufficient Boogie code to make the contradiction detectable
  ContradictoryEnsuresClauseFunc(x) - 1
}

method {:testEntry} CallContradictoryMethodMethod(x: int) returns (r: int)
  requires x > 1
  ensures r < 0
{
  var y := ContradictoryEnsuresClauseMethod(x);
  return y - 1;
}

// False antecedent requires clause
method {:testEntry} FalseAntecedentRequiresClauseMethod(x: int) returns (r: int)
  requires x*x < 0 ==> x == x + 1
  ensures r > x
{
  return x + 1;
}

// False antecedent assert statement.
method {:testEntry} FalseAntecedentAssertStatementMethod(x: int) {
  var y := x*x;
  assert y < 0 ==> x < 0;
}

// False antecedent ensures clause.
method {:testEntry} FalseAntecedentEnsuresClauseMethod(x: int) returns (r: int)
  ensures r < 0 ==> x < 0
{
  return x*x;
}

function {:testEntry} ObviouslyUnreachableIfExpressionBranchFunc(x: int): (r:int)
  requires x > 0
  ensures r > 0
{
  if x < 0
  then x - 1 // unreachable
  else x + 1
}

method {:testEntry} ObviouslyUnreachableIfStatementBranchMethod(x: int) returns (r:int)
  requires x > 0
  ensures r > 0
{
  if x < 0 {
    return x - 1; // unreachable
  } else {
    return x + 1;
  }
}

datatype T = A | B

function {:testEntry} ObviouslyUnreachableMatchExpressionCaseFunction(t: T): (r:int)
  requires t != A
  ensures r > 1 // alt: r > 0
{
  match t {
    case A => 1 // unreachable
    case B => 2
  }
}

method {:testEntry} ObviouslyUnreachableMatchStatementCaseMethod(t: T) returns (r:int)
  requires t != A
  ensures r > 1 // alt: r > 0
{
  match t {
    case A => return 1; // unreachable
    case B => return 2;
  }
}

method {:testEntry} ObviouslyUnreachableReturnStatementMethod(t: T) returns (r:int)
  requires t != A
    ensures r > 1 // alt: r > 0
  {
    if !t.A? {
      return 2;
    }

    return 1; // unreachable
  }

method {:testEntry} CalcStatementWithSideConditions(x: int) {
  calc == {
    x / 2;
    (x*2) / 4;
  }
}

method {:testEntry} DontWarnAboutVacuousAssertFalse(x: int) {
  assume x == x + 1;
  assert false;
}

class C {
  var x: int
}

function {:testEntry} GetX(c: C): int
  reads c
{
  c.x
}

method {:testEntry} DontWarnAboutUnusedAssumeTrue(x: int) {
  assume true;
  assert 1 + x == x + 1;
}

}
