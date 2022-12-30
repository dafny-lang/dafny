// RUN: %exits-with 2 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method M<T(==)>(a: T)

method P() {
  var x: (int, int, ghost int);
  M(x); // Disallowed. It's not possible to compile an equality function that also checks ghost components.
}
