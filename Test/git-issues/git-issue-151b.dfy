// RUN: %exits-with 2 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module A {
  method m() {}
  method p() {}
  function f(): int { 0 }
  function g(): int { 0 }
}

module B {
  method m() {}
  function f(): int { 0 }
  function g(): int { 0 }
}

module C {
  import opened A
  import opened B

  method p() {}
  function g(): int { 0 }

  method Bam() { m(); } // Ambiguous
  method Bay() { p(); } // OK
  function Baa(): int { f() } // Ambiguous
  function Bag(): int { g() } // OK
}

