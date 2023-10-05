// RUN: %baredafny verify --log-format:text --boogie -trackVerificationCoverage "%s" > "%t"
// RUN: %OutputCheck --file-to-check "%t" "%s"
// CHECK: Results for RedundantAssumeMethod \(correctness\)
// CHECK:     Proof dependencies:
// CHECK:       ProofDependencyLogging.dfy\(177,12\)-\(177,16\): assume statement
// CHECK:       ProofDependencyLogging.dfy\(178,12\)-\(178,12\): assertion always holds
//
// CHECK: Results for ContradictoryAssumeMethod \(correctness\)
// CHECK:     Proof dependencies:
// CHECK:       ProofDependencyLogging.dfy\(183,12\)-\(183,16\): assume statement
// CHECK:       ProofDependencyLogging.dfy\(184,12\)-\(184,16\): assume statement
//
// CHECK: Results for AssumeFalseMethod \(correctness\)
// CHECK:     Proof dependencies:
// CHECK:       ProofDependencyLogging.dfy\(192,12\)-\(192,12\): assume statement
//
// CHECK: Results for ObviouslyContradictoryRequiresFunc \(well-formedness\)
// CHECK:     Proof dependencies:
// CHECK:       ProofDependencyLogging.dfy\(198,12\)-\(198,16\): requires clause
// CHECK:       ProofDependencyLogging.dfy\(199,12\)-\(199,16\): requires clause
//
// CHECK: Results for ObviouslyContradictoryRequiresMethod \(correctness\)
// CHECK:     Proof dependencies:
// CHECK:       ProofDependencyLogging.dfy\(207,12\)-\(207,16\): requires clause
// CHECK:       ProofDependencyLogging.dfy\(208,12\)-\(208,16\): requires clause
//
// CHECK: Results for ObviouslyRedundantRequiresFunc \(well-formedness\)
// CHECK:     Proof dependencies:
// CHECK:       ProofDependencyLogging.dfy\(216,1\)-\(222,1\): function definition for ObviouslyRedundantRequiresFunc
// CHECK:       ProofDependencyLogging.dfy\(217,12\)-\(217,16\): requires clause
// CHECK:       ProofDependencyLogging.dfy\(219,11\)-\(219,15\): ensures clause
// CHECK:       ProofDependencyLogging.dfy\(221,3\)-\(221,7\): function call result
// CHECK:       ProofDependencyLogging.dfy\(221,5\)-\(221,5\): value always satisfies the subset constraints of 'nat'
//
// CHECK: Results for ObviouslyRedundantRequiresMethod \(correctness\)
// CHECK:     Proof dependencies:
// CHECK:       ProofDependencyLogging.dfy\(225,12\)-\(225,16\): requires clause
// CHECK:       ProofDependencyLogging.dfy\(227,11\)-\(227,15\): ensures clause
// CHECK:       ProofDependencyLogging.dfy\(229,12\)-\(229,12\): value always satisfies the subset constraints of 'nat'
// CHECK:       ProofDependencyLogging.dfy\(229,3\)-\(229,15\): assignment \(or return\)
//
// CHECK: Results for ObviouslyUnnecessaryRequiresFunc \(well-formedness\)
// CHECK:     Proof dependencies:
// CHECK:       ProofDependencyLogging.dfy\(237,21\)-\(237,21\): value always satisfies the subset constraints of 'nat'
// CHECK:       ProofDependencyLogging.dfy\(237,32\)-\(237,32\): value always satisfies the subset constraints of 'nat'
//
// CHECK: Results for ObviouslyUnnecessaryRequiresMethod \(correctness\)
// CHECK:     Proof dependencies:
// CHECK:       ProofDependencyLogging.dfy\(244,25\)-\(244,25\): value always satisfies the subset constraints of 'nat'
// CHECK:       ProofDependencyLogging.dfy\(244,48\)-\(244,48\): value always satisfies the subset constraints of 'nat'
//
// CHECK: Results for ObviouslyUnconstrainedCodeFunc \(well-formedness\)
// CHECK:     Proof dependencies:
// CHECK:       ProofDependencyLogging.dfy\(248,1\)-\(256,1\): function definition for ObviouslyUnconstrainedCodeFunc
// CHECK:       ProofDependencyLogging.dfy\(249,12\)-\(249,16\): requires clause
// CHECK:       ProofDependencyLogging.dfy\(250,11\)-\(250,17\): ensures clause
// CHECK:       ProofDependencyLogging.dfy\(252,12\)-\(252,16\): let expression binding RHS well-formed
// CHECK:       ProofDependencyLogging.dfy\(252,7\)-\(252,7\): let expression binding
// CHECK:       ProofDependencyLogging.dfy\(254,3\)-\(254,3\): let expression result
//
// CHECK: Results for ObviouslyUnconstrainedCodeMethod \(correctness\)
// CHECK:     Proof dependencies:
// CHECK:       ProofDependencyLogging.dfy\(259,12\)-\(259,16\): requires clause
// CHECK:       ProofDependencyLogging.dfy\(260,11\)-\(260,17\): ensures clause
// CHECK:       ProofDependencyLogging.dfy\(262,9\)-\(262,17\): assignment \(or return\)
// CHECK:       ProofDependencyLogging.dfy\(264,3\)-\(266,8\): assignment \(or return\)
//
// CHECK: Results for PartiallyRedundantRequiresFunc \(well-formedness\)
// CHECK:     Proof dependencies:
// CHECK:       ProofDependencyLogging.dfy\(270,1\)-\(275,1\): function definition for PartiallyRedundantRequiresFunc
// CHECK:       ProofDependencyLogging.dfy\(271,23\)-\(271,27\): requires clause
// CHECK:       ProofDependencyLogging.dfy\(272,11\)-\(272,15\): ensures clause
// CHECK:       ProofDependencyLogging.dfy\(274,3\)-\(274,7\): function call result
// CHECK:       ProofDependencyLogging.dfy\(274,5\)-\(274,5\): value always satisfies the subset constraints of 'nat'
//
// CHECK: Results for PartiallyUnnecessaryRequiresFunc \(well-formedness\)
// CHECK:     Proof dependencies:
// CHECK:       ProofDependencyLogging.dfy\(279,22\)-\(279,26\): requires clause
// CHECK:       ProofDependencyLogging.dfy\(282,21\)-\(282,21\): value always satisfies the subset constraints of 'nat'
// CHECK:       ProofDependencyLogging.dfy\(282,32\)-\(282,32\): value always satisfies the subset constraints of 'nat'
//
// CHECK: Results for MultiPartRedundantRequiresFunc \(well-formedness\)
// CHECK:     Proof dependencies:
// CHECK:       ProofDependencyLogging.dfy\(288,1\)-\(295,1\): function definition for MultiPartRedundantRequiresFunc
// CHECK:       ProofDependencyLogging.dfy\(291,12\)-\(291,17\): requires clause
// CHECK:       ProofDependencyLogging.dfy\(292,11\)-\(292,16\): ensures clause
// CHECK:       ProofDependencyLogging.dfy\(294,3\)-\(294,3\): function call result
//
// CHECK: Results for MultiPartRedundantRequiresMethod \(correctness\)
// CHECK:     Proof dependencies:
// CHECK:       ProofDependencyLogging.dfy\(300,12\)-\(300,17\): requires clause
// CHECK:       ProofDependencyLogging.dfy\(301,11\)-\(301,16\): ensures clause
//
// CHECK: Results for MultiPartContradictoryRequiresFunc \(well-formedness\)
// CHECK:     Proof dependencies:
// CHECK:       ProofDependencyLogging.dfy\(309,1\)-\(316,1\): function definition for MultiPartContradictoryRequiresFunc
// CHECK:       ProofDependencyLogging.dfy\(310,12\)-\(310,16\): requires clause
// CHECK:       ProofDependencyLogging.dfy\(311,12\)-\(311,16\): requires clause
// CHECK:       ProofDependencyLogging.dfy\(313,11\)-\(313,16\): ensures clause
// CHECK:       ProofDependencyLogging.dfy\(315,3\)-\(315,3\): function call result
//
// CHECK: Results for MultiPartContradictoryRequiresMethod \(correctness\)
// CHECK:     Proof dependencies:
// CHECK:       ProofDependencyLogging.dfy\(319,12\)-\(319,16\): requires clause
// CHECK:       ProofDependencyLogging.dfy\(320,12\)-\(320,16\): requires clause
// CHECK:       ProofDependencyLogging.dfy\(322,11\)-\(322,16\): ensures clause
//
// CHECK: Results for CallContradictoryFunctionFunc \(well-formedness\)
// CHECK:     Proof dependencies:
// CHECK:       ProofDependencyLogging.dfy\(336,1\)-\(342,1\): function definition for CallContradictoryFunctionFunc
// CHECK:       ProofDependencyLogging.dfy\(337,12\)-\(337,16\): requires clause
// CHECK:       ProofDependencyLogging.dfy\(338,11\)-\(338,15\): ensures clause
// CHECK:       ProofDependencyLogging.dfy\(341,3\)-\(341,3\): function precondition satisfied
// CHECK:       ProofDependencyLogging.dfy\(341,3\)-\(341,39\): function call result
//
// CHECK: Results for CallContradictoryMethodMethod \(correctness\)
// CHECK:     Proof dependencies:
// CHECK:       ProofDependencyLogging.dfy\(345,12\)-\(345,16\): requires clause
// CHECK:       ProofDependencyLogging.dfy\(348,9\)-\(348,47\): ensures clause at ProofDependencyLogging.dfy\(333,12\)-\(333,25\) from call
// CHECK:       ProofDependencyLogging.dfy\(348,9\)-\(348,47\): ensures clause at ProofDependencyLogging.dfy\(333,12\)-\(333,25\) from call
// CHECK:       ProofDependencyLogging.dfy\(348,9\)-\(348,47\): requires clause at ProofDependencyLogging.dfy\(332,12\)-\(332,16\) from call
//
// CHECK: Results for FalseAntecedentRequiresClauseMethod \(correctness\)
// CHECK:     Proof dependencies:
// CHECK:       ProofDependencyLogging.dfy\(357,3\)-\(357,15\): assignment \(or return\)
//
// CHECK: Results for FalseAntecedentAssertStatementMethod \(correctness\)
// CHECK:     Proof dependencies:
// CHECK:       ProofDependencyLogging.dfy\(362,9\)-\(362,15\): assignment \(or return\)
// CHECK:       ProofDependencyLogging.dfy\(363,20\)-\(363,20\): assertion always holds
//
// CHECK: Results for FalseAntecedentEnsuresClauseMethod \(correctness\)
// CHECK:     Proof dependencies:
// CHECK:       ProofDependencyLogging.dfy\(368,11\)-\(368,25\): ensures clause
// CHECK:       ProofDependencyLogging.dfy\(370,3\)-\(370,13\): assignment \(or return\)
//
// CHECK: Results for ObviouslyUnreachableIfExpressionBranchFunc \(well-formedness\)
// CHECK:     Proof dependencies:
// CHECK:       ProofDependencyLogging.dfy\(373,1\)-\(380,1\): function definition for ObviouslyUnreachableIfExpressionBranchFunc
// CHECK:       ProofDependencyLogging.dfy\(374,12\)-\(374,16\): requires clause
// CHECK:       ProofDependencyLogging.dfy\(375,11\)-\(375,15\): ensures clause
// CHECK:       ProofDependencyLogging.dfy\(379,8\)-\(379,12\): if expression else branch
//
// CHECK: Results for ObviouslyUnreachableIfStatementBranchMethod \(correctness\)
// CHECK:     Proof dependencies:
// CHECK:       ProofDependencyLogging.dfy\(383,12\)-\(383,16\): requires clause
// CHECK:       ProofDependencyLogging.dfy\(384,11\)-\(384,15\): ensures clause
// CHECK:       ProofDependencyLogging.dfy\(389,5\)-\(389,17\): assignment \(or return\)
//
// CHECK: Results for ObviouslyUnreachableMatchExpressionCaseFunction \(well-formedness\)
//
// CHECK:     Proof dependencies:
// CHECK:       ProofDependencyLogging.dfy\(395,1\)-\(403,1\): function definition for ObviouslyUnreachableMatchExpressionCaseFunction
// CHECK:       ProofDependencyLogging.dfy\(396,12\)-\(396,17\): requires clause
// CHECK:       ProofDependencyLogging.dfy\(397,11\)-\(397,15\): ensures clause
// CHECK:       ProofDependencyLogging.dfy\(401,15\)-\(401,15\): match expression branch result
//
// CHECK: Results for ObviouslyUnreachableMatchStatementCaseMethod \(correctness\)
// CHECK:     Proof dependencies:
// CHECK:       ProofDependencyLogging.dfy\(406,12\)-\(406,17\): requires clause
// CHECK:       ProofDependencyLogging.dfy\(407,11\)-\(407,15\): ensures clause
// CHECK:       ProofDependencyLogging.dfy\(411,15\)-\(411,23\): assignment \(or return\)
//
// CHECK: Results for ObviouslyUnreachableReturnStatementMethod \(correctness\)
// CHECK:     Proof dependencies:
// CHECK:       ProofDependencyLogging.dfy\(416,12\)-\(416,17\): requires clause
// CHECK:       ProofDependencyLogging.dfy\(417,13\)-\(417,17\): ensures clause
// CHECK:       ProofDependencyLogging.dfy\(420,7\)-\(420,15\): assignment \(or return\)




method RedundantAssumeMethod(n: int)
{
    // either one or the other assumption shouldn't be covered
    assume n > 4;
    assume n > 3;
    assert n > 1;
}

method ContradictoryAssumeMethod(n: int)
{
    assume n > 0;
    assume n < 0;
    assume n == 5; // shouldn't be covered
    assert n < 10; // shouldn't be covered
}

method AssumeFalseMethod(n: int)
{
    assume n == 15; // shouldn't be covered
    assume false;
    assert n < 10; // shouldn't be covered
}

// Obvious contradiction in requires clauses.
function ObviouslyContradictoryRequiresFunc(x: nat): (r: nat)
  requires x > 10
  requires x < 10
  ensures r < x // only provable vacuously 
{
  assert x == 10; // contradicts both requires clauses
  x - 1 // not necessarily a valid nat
}

method ObviouslyContradictoryRequiresMethod(x: nat) returns (r: nat)
  requires x > 10
  requires x < 10
  ensures r < x // only provable vacuously
{
  assert x == 10; // contradicts both requires clauses
  return x - 1; // not necessarily a valid nat
}

// Obvious redundancy in requires clauses.
function ObviouslyRedundantRequiresFunc(x: nat): (r: nat)
  requires x < 10
  requires x < 100 // implied by previous requires clause
  ensures r < 11 // should cause body and first requires clause to be covered
{
  x + 1
}

method ObviouslyRedundantRequiresMethod(x: nat) returns (r: nat)
  requires x < 10
  requires x < 100 // implied by previous requires clause
  ensures r < 11 // should cause body and first requires clause to be covered
{
  return x + 1;
}

// Obviously unnecessary requires clauses.
function ObviouslyUnnecessaryRequiresFunc(x: nat): (r: nat)
  requires x < 10 // not required for the proof
{
  // cause at least a little proof work to be necessary, for nat bounds
  if (x > 5) then x + 2 else x + 1
}

method ObviouslyUnnecessaryRequiresMethod(x: nat) returns (r: nat)
  requires x < 10 // not required for the proof
{
  // cause at least a little proof work to be necessary, for nat bounds
  if (x > 5) { return x + 2; } else { return x + 1; }
}

// Code obviously not constrained by ensures clause.
function ObviouslyUnconstrainedCodeFunc(x: int): (r: (int, int))
  requires x > 10
  ensures r.0 > 10
{
  var a := x + 1; // constrained by ensures clause
  var b := x - 1; // not constrained by ensures clause 
  (a,
   b)
}

method ObviouslyUnconstrainedCodeMethod(x: int) returns (r: (int, int))
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
function PartiallyRedundantRequiresFunc(x: nat): (r: nat)
  requires x < 100 && x < 10 // LHS implied by RHS
  ensures r < 11 // should cause body and RHS clause to be covered
{
  x + 1
}

// Partly unnecessary requires clause.
function PartiallyUnnecessaryRequiresFunc(x: int): (r: nat)
  requires x < 10 && x > 0 // RHS required for proof, but not LHS
{
  // cause at least a little proof work to be necessary, for nat bounds
  if (x > 5) then x - 1 else x + 1
}


// Redundancy of one requires clause due to at least two others, with at least
// one of the three being partly in a separately-defined function.
function MultiPartRedundantRequiresFunc(x: int): (r: int)
  requires x > 10
  requires x < 12
  requires x == 11 // implied by the previous two, but neither individually
  ensures r == 11
{
  x
}

method MultiPartRedundantRequiresMethod(x: int) returns (r: int)
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
function MultiPartContradictoryRequiresFunc(x: int, y: int): (r: int)
  requires x > 10
  requires x < 12
  requires y != 11 // contradicts the previous two
  ensures r == 11 // provable from first two preconditions, but shouldn't be covered
{
  x
}

method MultiPartContradictoryRequiresMethod(x: int, y: int) returns (r: int)
  requires x > 10
  requires x < 12
  requires y != 11 // contradicts the previous two
  ensures r == 11 // provable from first two preconditions, but shouldn't be covered
{
  return x;
}

function ContradictoryEnsuresClauseFunc(x: int): (r: int)
  requires x > 1
  ensures  r > x && r < 0

method ContradictoryEnsuresClauseMethod(x: int) returns (r: int)
  requires x > 1
  ensures  r > x && r < 0

// Call function that has contradictory ensures clauses.
function CallContradictoryFunctionFunc(x: int): (r: int)
  requires x > 1
  ensures r < 0
{
  // TODO: Dafny doesn't generate sufficient Boogie code to make the contradiction detectable
  ContradictoryEnsuresClauseFunc(x) - 1
}

method CallContradictoryMethodMethod(x: int) returns (r: int)
  requires x > 1
  ensures r < 0
{
  var y := ContradictoryEnsuresClauseMethod(x);
  return y - 1;
}

// False antecedent requires clause
method FalseAntecedentRequiresClauseMethod(x: int) returns (r: int)
  requires x*x < 0 ==> x == x + 1
  ensures r > x
{
  return x + 1;
}

// False antecedent assert statement.
method FalseAntecedentAssertStatementMethod(x: int) {
  var y := x*x;
  assert y < 0 ==> x < 0;
}

// False antecedent ensures clause.
method FalseAntecedentEnsuresClauseMethod(x: int) returns (r: int)
  ensures r < 0 ==> x < 0
{
  return x*x;
}

function ObviouslyUnreachableIfExpressionBranchFunc(x: int): (r:int)
  requires x > 0
  ensures r > 0
{
  if x < 0
  then x - 1 // unreachable
  else x + 1
}

method ObviouslyUnreachableIfStatementBranchMethod(x: int) returns (r:int)
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

function ObviouslyUnreachableMatchExpressionCaseFunction(t: T): (r:int)
  requires t != A
  ensures r > 1 // alt: r > 0
{
  match t {
    case A => 1 // unreachable
    case B => 2
  }
}

method ObviouslyUnreachableMatchStatementCaseMethod(t: T) returns (r:int)
  requires t != A
  ensures r > 1 // alt: r > 0
{
  match t {
    case A => return 1; // unreachable
    case B => return 2;
  }
}

method ObviouslyUnreachableReturnStatementMethod(t: T) returns (r:int)
  requires t != A
    ensures r > 1 // alt: r > 0
  {
    if !t.A? {
      return 2;
    }

    return 1; // unreachable
  }

method CalcStatementWithSideConditions(x: int) {
  calc == {
    x / 2;
    (x*2) / 4;
  }
}

method DontWarnAboutVacuousAssertFalse(x: int) {
  assume x == x + 1;
  assert false;
}

// CHECK: Results for GetX \(well-formedness\)
// CHECK:     Proof dependencies:
// CHECK:       ProofDependencyLogging.dfy\(449,5\)-\(449,5\): target object is never null

class C {
  var x: int
}

function GetX(c: C): int
  reads c
{
  c.x
}

method DontWarnAboutUnusedAssumeTrue(x: int) {
  assume true;
  assert 1 + x == x + 1;
}
