// RUN: %verify --type-system-refresh --allow-axioms --bprint:%t.bpl --isolate-assertions --boogie "/printPruned:%S/pruned" %s > %t
// RUN: %diff "%s.expect" "%t"

function StmtExprValueAndEnsures(): int
  ensures ValueAndEnsures() == 42 
{
  assert true; 42
}

function ExpressionWFVersusFunctionEnsures(): int 
  ensures 10 == 11 // no error, since the statement expression can be used for the ensures clause
{
  assume false; 10
}

function ExpressionWFAndLet(): int 
{
  var x := assume false; 10; 
  assert false; // error, since the statement expression does not leak outside of the let.
  x
}

method Bar() {
  var x := assume false; 3;
  assert false; // error
}

