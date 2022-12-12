// RUN: %exits-with 2 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module M {}
const x := 10

export provides x  // No exports allowed at top-level

module N {
  import M
}
