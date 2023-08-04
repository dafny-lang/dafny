// RUN: %exits-with 2 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

predicate P(x: bool)
type WE = e: (int, int) | P()
