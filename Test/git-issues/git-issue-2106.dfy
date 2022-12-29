// RUN: %exits-with 2 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

predicate method P(x: bool)
type WE = e: (int, int) | P()
