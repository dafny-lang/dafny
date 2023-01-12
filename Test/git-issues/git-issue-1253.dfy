// RUN: %exits-with 2 %dafny "%s" > "%t"
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
