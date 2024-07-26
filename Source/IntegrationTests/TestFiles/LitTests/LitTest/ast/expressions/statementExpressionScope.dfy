// RUN: ! %verify --type-system-refresh --allow-axioms --bprint:%t.bpl --isolate-assertions %s > %t
// RUN: %diff "%s.expect" "%t"

function StatementExpressionValueAndEnsures(): int
  ensures StatementExpressionValueAndEnsures() == 42 
{
  assert true; 42
}

function StatementExpressionAssumeAndFunctionEnsures(): int 
  ensures 10 == 11 // no error, since the statement expression can be used for the ensures clause
{
  assume false; 10
}

function StatementExpressionAssumeAndFunctionEnsures(): int 
  ensures 10 == 11 // error, since the assume false does not leak
{
  var x := (assume false; 10); x
}

function StatementExpressionAndSubsetResult(): nat 
  // no error, since the statement expression can be used for the return type subset constraint
{
  assume -1 > 0; -1
}

method StatementExpressionAndSubsetLocal() 
  // no error, since the statement expression can be used for the local variable type subset constraint
{
  var x: nat := assume -1 > 0; -1;
}

predicate P(x: int)
method NeedsP(x: int) requires P(x)

method StatementExpressionAndPrecondition(x: int) 
{
  NeedsP(assume P(x); x); // no error, since the statement expression can be used for the requires clause
}

function StatementExpressionAssumeDoesNotEscapeLetBinding(): int 
{
  var x := assume false; 10; 
  assert false; // error, since the statement expression does not leak outside of the let.
  x
}

method StatementExpressionAssumeDoesNotEscapeAssignment() {
  var x := assume false; 3;
  assert false; // error, since the statement expression does not leak outside of the assignment.
}

