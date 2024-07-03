// RUN: ! %verify --type-system-refresh --allow-axioms --bprint:%t.bpl --isolate-assertions --boogie "/printPruned:%S/pruned" %s > %t
// RUN: %diff "%s.expect" "%t"

function P(x: int): bool {
  true
}

method RevealExpressionScope()
{
  hide *;
  var c := (var x: bool :| (reveal P; assert P(4); x); 
            assert P(5); x); // error
}