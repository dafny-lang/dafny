// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"


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

