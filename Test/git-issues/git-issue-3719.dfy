// RUN: %exits-with 1 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Function want to verify something about
opaque function inc(x:nat) : nat { x + 1 }

// Intermediatary to force lambda
predicate Check(p: ()->bool) { p() }

method test() {
    assert Check(() => inc(1) == 2);
}