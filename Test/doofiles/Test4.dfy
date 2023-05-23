// RUN: %baredafny build -t:lib "%s" --output "%S/test" > "%t"
// RUN: %baredafny resolve "%s"  "%S/test.doo" >> "%t"
// RUN: %diff "%s.expect" "%t"
// XFAIL: *

// Combining a file with a .doo of itself -- was a crash

const c := 42
