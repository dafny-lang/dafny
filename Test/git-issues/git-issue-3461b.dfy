// RUN: %exits-with 4 %baredafny verify %verifyargs "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

const d := 42
opaque const c := 5 // OK
method z() {
  assert c == 5; // No - opaque
}
method p() {
  assert d == 42; // OK
}
