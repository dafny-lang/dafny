// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"


module M1 {
  import M2.C
  export
    provides
      C
  module M2 {
    const C: int
  }
}
