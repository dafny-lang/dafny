// RUN: %exits-with 4 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Function want to verify something about
opaque function inc(x:nat) : nat { x + 1 }

// Intermediatary to force lambda
predicate CheckThis(p: ()->bool) { p() }

opaque const one: nat := 1

method test() {
  assert CheckThis(() => inc(1) == 2);  // Error on this one
}

method test2() {
  reveal inc();
  assert CheckThis(() => inc(1) == 2); // No error on this one
}