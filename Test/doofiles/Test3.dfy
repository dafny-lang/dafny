// RUN: %baredafny build -t:lib "%s" --output "%S/test" > "%t"
// RUN: %baredafny resolve "%S/Test3a.dfy"  "%S/test.doo" >> "%t"
// RUN: %diff "%s.expect" "%t"

// Output file does not have a .doo suffix; test.doo created

const c := 42
