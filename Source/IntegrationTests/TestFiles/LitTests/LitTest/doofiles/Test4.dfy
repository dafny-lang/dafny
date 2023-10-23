// RUN: %baredafny build -t:lib --use-basename-for-filename "%s" --output "%S/test2" > "%t"
// RUN: %baredafny resolve --use-basename-for-filename "%s"  "%S/test2.doo" >> "%t"
// RUN: %diff "%s.expect" "%t"
// XFAIL: *

// Combining a file with a .doo of itself -- was a crash

const c := 42
