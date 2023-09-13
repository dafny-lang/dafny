// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"
// RUN: %diff "%s.expect" "%t"

ghost predicate P() {
  forall m:mode :: m == m
}
