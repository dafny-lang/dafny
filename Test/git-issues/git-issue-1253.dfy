// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"
// RUN: %diff "%s.expect" "%t"

module M1 {
  import M2.C
  export
    provides
      C
  module M2 {
    const C: int
  }
}
