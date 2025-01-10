// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"


method M<T(==)>(a: T)

method P() {
  var x: (int, int, ghost int);
  M(x); // Disallowed. It's not possible to compile an equality function that also checks ghost components.
}
