// RUN: %dafny_0 /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module A {
  type T = int
}

module B refines A {
  type T = int
}
