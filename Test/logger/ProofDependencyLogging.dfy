// RUN: %baredafny verify --log-format:text --boogie -trackVerificationCoverage "%s" > "%t"
// RUN: %OutputCheck --file-to-check "%t" "%s"
// CHECK: Results for RedundantAssumeMethod \(correctness\)
// CHECK:     Proof dependencies:
// CHECK:       ProofDependencyLogging.dfy\(177,11\)-\(177,15\): assume statement
// CHECK:       ProofDependencyLogging.dfy\(178,11\)-\(178,11\): assertion always holds
//
// CHECK: Results for ContradictoryAssumeMethod \(correctness\)
// CHECK:     Proof dependencies:
// CHECK:       ProofDependencyLogging.dfy\(183,11\)-\(183,15\): assume statement
// CHECK:       ProofDependencyLogging.dfy\(184,11\)-\(184,15\): assume statement
//
// CHECK: Results for AssumeFalseMethod \(correctness\)
// CHECK:     Proof dependencies:
// CHECK:       ProofDependencyLogging.dfy\(192,11\)-\(192,11\): assume statement
//
// CHECK: Results for ObviouslyContradictoryRequiresFunc \(well-formedness\)
// CHECK:     Proof dependencies:
// CHECK:       ProofDependencyLogging.dfy\(198,11\)-\(198,15\): requires clause
// CHECK:       ProofDependencyLogging.dfy\(199,11\)-\(199,15\): requires clause
//
// CHECK: Results for ObviouslyContradictoryRequiresMethod \(correctness\)
// CHECK:     Proof dependencies:
// CHECK:       ProofDependencyLogging.dfy\(207,11\)-\(207,15\): requires clause
// CHECK:       ProofDependencyLogging.dfy\(208,11\)-\(208,15\): requires clause
//
// CHECK: Results for ObviouslyRedundantRequiresFunc \(well-formedness\)
// CHECK:     Proof dependencies:
// CHECK:       ProofDependencyLogging.dfy\(216,0\)-\(222,0\): function definition for ObviouslyRedundantRequiresFunc
// CHECK:       ProofDependencyLogging.dfy\(217,11\)-\(217,15\): requires clause
// CHECK:       ProofDependencyLogging.dfy\(219,10\)-\(219,14\): ensures clause
// CHECK:       ProofDependencyLogging.dfy\(221,2\)-\(221,6\): function call result
// CHECK:       ProofDependencyLogging.dfy\(221,4\)-\(221,4\): value always satisfies the subset constraints of 'nat'
//
// CHECK: Results for ObviouslyRedundantRequiresMethod \(correctness\)
// CHECK:     Proof dependencies:
// CHECK:       ProofDependencyLogging.dfy\(225,11\)-\(225,15\): requires clause
// CHECK:       ProofDependencyLogging.dfy\(227,10\)-\(227,14\): ensures clause
// CHECK:       ProofDependencyLogging.dfy\(229,11\)-\(229,11\): value always satisfies the subset constraints of 'nat'
// CHECK:       ProofDependencyLogging.dfy\(229,2\)-\(229,14\): assignment \(or return\)
//
// CHECK: Results for ObviouslyUnnecessaryRequiresFunc \(well-formedness\)
// CHECK:     Proof dependencies:
// CHECK:       ProofDependencyLogging.dfy\(237,20\)-\(237,20\): value always satisfies the subset constraints of 'nat'
// CHECK:       ProofDependencyLogging.dfy\(237,31\)-\(237,31\): value always satisfies the subset constraints of 'nat'
//
// CHECK: Results for ObviouslyUnnecessaryRequiresMethod \(correctness\)
// CHECK:     Proof dependencies:
// CHECK:       ProofDependencyLogging.dfy\(244,24\)-\(244,24\): value always satisfies the subset constraints of 'nat'
// CHECK:       ProofDependencyLogging.dfy\(244,47\)-\(244,47\): value always satisfies the subset constraints of 'nat'
//
// CHECK: Results for ObviouslyUnconstrainedCodeFunc \(well-formedness\)
// CHECK:     Proof dependencies:
// CHECK:       ProofDependencyLogging.dfy\(248,0\)-\(256,0\): function definition for ObviouslyUnconstrainedCodeFunc
// CHECK:       ProofDependencyLogging.dfy\(249,11\)-\(249,15\): requires clause
// CHECK:       ProofDependencyLogging.dfy\(250,10\)-\(250,16\): ensures clause
// CHECK:       ProofDependencyLogging.dfy\(252,11\)-\(252,15\): let expression binding RHS well-formed
// CHECK:       ProofDependencyLogging.dfy\(252,6\)-\(252,6\): let expression binding
// CHECK:       ProofDependencyLogging.dfy\(254,2\)-\(254,2\): let expression result
//
// CHECK: Results for ObviouslyUnconstrainedCodeMethod \(correctness\)
// CHECK:     Proof dependencies:
// CHECK:       ProofDependencyLogging.dfy\(259,11\)-\(259,15\): requires clause
// CHECK:       ProofDependencyLogging.dfy\(260,10\)-\(260,16\): ensures clause
// CHECK:       ProofDependencyLogging.dfy\(262,8\)-\(262,16\): assignment \(or return\)
// CHECK:       ProofDependencyLogging.dfy\(264,2\)-\(266,7\): assignment \(or return\)
//
// CHECK: Results for PartiallyRedundantRequiresFunc \(well-formedness\)
// CHECK:     Proof dependencies:
// CHECK:       ProofDependencyLogging.dfy\(270,0\)-\(275,0\): function definition for PartiallyRedundantRequiresFunc
// CHECK:       ProofDependencyLogging.dfy\(271,22\)-\(271,26\): requires clause
// CHECK:       ProofDependencyLogging.dfy\(272,10\)-\(272,14\): ensures clause
// CHECK:       ProofDependencyLogging.dfy\(274,2\)-\(274,6\): function call result
// CHECK:       ProofDependencyLogging.dfy\(274,4\)-\(274,4\): value always satisfies the subset constraints of 'nat'
//
// CHECK: Results for PartiallyUnnecessaryRequiresFunc \(well-formedness\)
// CHECK:     Proof dependencies:
// CHECK:       ProofDependencyLogging.dfy\(279,21\)-\(279,25\): requires clause
// CHECK:       ProofDependencyLogging.dfy\(282,20\)-\(282,20\): value always satisfies the subset constraints of 'nat'
// CHECK:       ProofDependencyLogging.dfy\(282,31\)-\(282,31\): value always satisfies the subset constraints of 'nat'
//
// CHECK: Results for MultiPartRedundantRequiresFunc \(well-formedness\)
// CHECK:     Proof dependencies:
// CHECK:       ProofDependencyLogging.dfy\(288,0\)-\(295,0\): function definition for MultiPartRedundantRequiresFunc
// CHECK:       ProofDependencyLogging.dfy\(291,11\)-\(291,16\): requires clause
// CHECK:       ProofDependencyLogging.dfy\(292,10\)-\(292,15\): ensures clause
// CHECK:       ProofDependencyLogging.dfy\(294,2\)-\(294,2\): function call result
//
// CHECK: Results for MultiPartRedundantRequiresMethod \(correctness\)
// CHECK:     Proof dependencies:
// CHECK:       ProofDependencyLogging.dfy\(300,11\)-\(300,16\): requires clause
// CHECK:       ProofDependencyLogging.dfy\(301,10\)-\(301,15\): ensures clause
//
// CHECK: Results for MultiPartContradictoryRequiresFunc \(well-formedness\)
// CHECK:     Proof dependencies:
// CHECK:       ProofDependencyLogging.dfy\(309,0\)-\(316,0\): function definition for MultiPartContradictoryRequiresFunc
// CHECK:       ProofDependencyLogging.dfy\(310,11\)-\(310,15\): requires clause
// CHECK:       ProofDependencyLogging.dfy\(311,11\)-\(311,15\): requires clause
// CHECK:       ProofDependencyLogging.dfy\(313,10\)-\(313,15\): ensures clause
// CHECK:       ProofDependencyLogging.dfy\(315,2\)-\(315,2\): function call result
//
// CHECK: Results for MultiPartContradictoryRequiresMethod \(correctness\)
// CHECK:     Proof dependencies:
// CHECK:       ProofDependencyLogging.dfy\(319,11\)-\(319,15\): requires clause
// CHECK:       ProofDependencyLogging.dfy\(320,11\)-\(320,15\): requires clause
// CHECK:       ProofDependencyLogging.dfy\(322,10\)-\(322,15\): ensures clause
//
// CHECK: Results for CallContradictoryFunctionFunc \(well-formedness\)
// CHECK:     Proof dependencies:
// CHECK:       ProofDependencyLogging.dfy\(336,0\)-\(342,0\): function definition for CallContradictoryFunctionFunc
// CHECK:       ProofDependencyLogging.dfy\(337,11\)-\(337,15\): requires clause
// CHECK:       ProofDependencyLogging.dfy\(338,10\)-\(338,14\): ensures clause
// CHECK:       ProofDependencyLogging.dfy\(341,2\)-\(341,2\): function precondition satisfied
// CHECK:       ProofDependencyLogging.dfy\(341,2\)-\(341,38\): function call result
//
// CHECK: Results for CallContradictoryMethodMethod \(correctness\)
// CHECK:     Proof dependencies:
// CHECK:       ProofDependencyLogging.dfy\(345,11\)-\(345,15\): requires clause
// CHECK:       ProofDependencyLogging.dfy\(348,8\)-\(348,46\): ensures clause at ProofDependencyLogging.dfy\(333,11\)-\(333,24\) from call
// CHECK:       ProofDependencyLogging.dfy\(348,8\)-\(348,46\): ensures clause at ProofDependencyLogging.dfy\(333,11\)-\(333,24\) from call
// CHECK:       ProofDependencyLogging.dfy\(348,8\)-\(348,46\): requires clause at ProofDependencyLogging.dfy\(332,11\)-\(332,15\) from call
//
// CHECK: Results for FalseAntecedentRequiresClauseMethod \(correctness\)
// CHECK:     Proof dependencies:
// CHECK:       ProofDependencyLogging.dfy\(357,2\)-\(357,14\): assignment \(or return\)
//
// CHECK: Results for FalseAntecedentAssertStatementMethod \(correctness\)
// CHECK:     Proof dependencies:
// CHECK:       ProofDependencyLogging.dfy\(362,8\)-\(362,14\): assignment \(or return\)
// CHECK:       ProofDependencyLogging.dfy\(363,19\)-\(363,19\): assertion always holds
//
// CHECK: Results for FalseAntecedentEnsuresClauseMethod \(correctness\)
// CHECK:     Proof dependencies:
// CHECK:       ProofDependencyLogging.dfy\(368,10\)-\(368,24\): ensures clause
// CHECK:       ProofDependencyLogging.dfy\(370,2\)-\(370,12\): assignment \(or return\)
//
// CHECK: Results for ObviouslyUnreachableIfExpressionBranchFunc \(well-formedness\)
// CHECK:     Proof dependencies:
// CHECK:       ProofDependencyLogging.dfy\(373,0\)-\(380,0\): function definition for ObviouslyUnreachableIfExpressionBranchFunc
// CHECK:       ProofDependencyLogging.dfy\(374,11\)-\(374,15\): requires clause
// CHECK:       ProofDependencyLogging.dfy\(375,10\)-\(375,14\): ensures clause
// CHECK:       ProofDependencyLogging.dfy\(379,7\)-\(379,11\): if expression else branch
//
// CHECK: Results for ObviouslyUnreachableIfStatementBranchMethod \(correctness\)
// CHECK:     Proof dependencies:
// CHECK:       ProofDependencyLogging.dfy\(383,11\)-\(383,15\): requires clause
// CHECK:       ProofDependencyLogging.dfy\(384,10\)-\(384,14\): ensures clause
// CHECK:       ProofDependencyLogging.dfy\(389,4\)-\(389,16\): assignment \(or return\)
//
// CHECK: Results for ObviouslyUnreachableMatchExpressionCaseFunction \(well-formedness\)
//
// CHECK:     Proof dependencies:
// CHECK:       ProofDependencyLogging.dfy\(395,0\)-\(403,0\): function definition for ObviouslyUnreachableMatchExpressionCaseFunction
// CHECK:       ProofDependencyLogging.dfy\(396,11\)-\(396,16\): requires clause
// CHECK:       ProofDependencyLogging.dfy\(397,10\)-\(397,14\): ensures clause
// CHECK:       ProofDependencyLogging.dfy\(401,14\)-\(401,14\): match expression branch result
//
// CHECK: Results for ObviouslyUnreachableMatchStatementCaseMethod \(correctness\)
// CHECK:     Proof dependencies:
// CHECK:       ProofDependencyLogging.dfy\(406,11\)-\(406,16\): requires clause
// CHECK:       ProofDependencyLogging.dfy\(407,10\)-\(407,14\): ensures clause
// CHECK:       ProofDependencyLogging.dfy\(411,14\)-\(411,22\): assignment \(or return\)
//
// CHECK: Results for ObviouslyUnreachableReturnStatementMethod \(correctness\)
// CHECK:     Proof dependencies:
// CHECK:       ProofDependencyLogging.dfy\(416,11\)-\(416,16\): requires clause
// CHECK:       ProofDependencyLogging.dfy\(417,12\)-\(417,16\): ensures clause
// CHECK:       ProofDependencyLogging.dfy\(420,6\)-\(420,14\): assignment \(or return\)




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
