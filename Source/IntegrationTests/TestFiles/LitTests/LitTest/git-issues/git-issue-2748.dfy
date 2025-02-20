// RUN: %verify --type-system-refresh=false --general-newtypes=false "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function f(x: int): int { 10 - x * x }

function BindingGuardTestStmt(): int {
  var x: nat := 1;
  assert true by {
    if i :| 0 <= i < 10 && (f(i) == f(i+1) || f(i) == f(i+2)) {
    }
  }
  2
}

function BindingGuardTestExpr(): int {
  var x: nat := 1;
  assert true by {
    var x := if i :| 0 <= i < 10 && (f(i) == f(i+1) || f(i) == f(i+2)) then 1 else 0;
  }
  2
}
