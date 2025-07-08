// RUN: %build -t:lib "%s" --output "%S/test2" > "%t"
// RUN: ! %resolve "%s"  "%S/test2.doo" >> "%t"
// RUN: %diff "%s.expect" "%t"

// Combining a file with a .doo of itself -- was a crash

const c := 42
