// RUN: %exits-with 2 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module A {
  method m() {}
  method p() {}
  ghost function f(): int { 0 }
  ghost function g(): int { 0 }
}

module B {
  method m() {}
  ghost function f(): int { 0 }
  ghost function g(): int { 0 }
}

module C {
  import opened A
  import opened B

  method p() {}
  ghost function g(): int { 0 }

  method Bam() { m(); } // Ambiguous
  method Bay() { p(); } // OK
  ghost function Baa(): int { f() } // Ambiguous
  ghost function Bag(): int { g() } // OK
}

