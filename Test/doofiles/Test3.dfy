// RUN: %baredafny build -t:lib  --use-basename-for-filename "%s" --output "%S/test" > "%t"
// RUN: %baredafny resolve --use-basename-for-filename "%S/Test3a.dfy"  "%S/test.doo" >> "%t"
// RUN: %diff "%s.expect" "%t"

// Output file does not have a .doo suffix; test.doo created

const c := 42
