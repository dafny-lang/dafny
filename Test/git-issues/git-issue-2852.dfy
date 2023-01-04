// RUN: %dafny -compile:3 -compileTarget:cs "%s" > "%t"
// RUN: %dafny -noVerify -compile:4 -compileTarget:js "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

// Returns a function that computes the sum of n consecutive integers starting at pos
function method Sum(
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