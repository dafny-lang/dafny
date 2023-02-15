// RUN: %exits-with 2 %resolve "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

opaque method m() {} // NO

opaque const c := 5 // OK

opaque function f(): int { 42 } // OK
opaque predicate p() { true } // OK

opaque class A {} // NO
opaque datatype D = D // NO
opaque newtype N = int // NO
opaque type P = i | i >= 0 // NO

method z() {
  opaque var j: int // NO
}
