// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"


ghost predicate P() {
  forall m:mode :: m == m
}
