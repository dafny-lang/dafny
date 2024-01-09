// RUN: %exits-with 2 %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// The two errors below had previously slipped by the resolver, causing malformed compiled code.

datatype Outer = Outer(ghost inner: Inner)
datatype Inner = Inner(x: int)

method M(o: Outer) returns (r: int) {
  match o
  case Outer(Inner(x)) =>
    r := x; // error: cannot assign ghost x to non-ghost r
}

function F(o: Outer): int {
  match o
  case Outer(Inner(x)) =>
    x // error: cannot use ghost x in non-ghost context
}
