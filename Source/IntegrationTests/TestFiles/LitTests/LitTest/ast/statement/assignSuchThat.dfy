// RUN: %verify %s &> "%t"
// RUN: %diff "%s.expect" "%t"

method ByClause(b: bool) {
  var r: int :| false by {
    assume {:axiom} false;
  }
}

function F(x: int): int
method ByClauseSeparateAssignment() {
  var a;
  a :| F(a) == 2 by {
    assume {:axiom} F(10) == 2;
  }
}