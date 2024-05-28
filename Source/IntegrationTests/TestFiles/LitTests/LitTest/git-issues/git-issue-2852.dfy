// NONUNIFORM: regression test
// RUN: %run --target cs "%s" > "%t"
// RUN: %run --no-verify --target js "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

// Returns a function that computes the sum of n consecutive integers starting at pos
function Sum(
  ghost remaining: nat,
  n: nat
): (p: nat -> nat)
  decreases remaining
  requires remaining == n
{
  (pos: nat) =>
    var x: nat := if n == 0 then 0 else Sum(remaining - 1, n - 1)(pos+1) + pos;
    x
}
method Main() {
  print Sum(5, 5)(10);
}