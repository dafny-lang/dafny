// RUN: %exits-with 4 %dafny /compile:1 /errorLimit:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
ghost predicate EvenNat(n: nat) { n % 2 == 0 }
ghost predicate TrueInt(x: int) { true }

method NatTypeInferenceType() {
  // These behave as they had before
  assert forall n: nat :: EvenNat(n) ==> TrueInt(n); // correct, since n is nat
  assert forall x: int :: EvenNat(x) ==> TrueInt(x); // precondition violation, since EvenNat expects a nat and x is int
  assert forall x: int :: 0 <= x && EvenNat(x) ==> TrueInt(x); // good
  assert forall x: int :: EvenNat(x) && 0 <= x ==> TrueInt(x); // precondition violation (good)
  assert forall n :: EvenNat(n) ==> TrueInt(n); // since n is inferred to be an int, an precondition violation is reported

  // In the following, n should be inferred as a nat
  assert forall n | EvenNat(n) :: n == n;
  assert forall n :: EvenNat(n) ==> true;
}