// RUN: %exits-with 4 %verify --show-inference "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This tests shows that, since quantifiers are split, it becomes possible to know more precisely what part of a precondition did not hold at the call site.

method f()
  requires forall y :: y > 0 && y < 0 {
}

method g(x: int) {
  f();
}

ghost function gf(): int
  requires forall y :: y > 0 && y < 0 {
    1
}

ghost function gg(x: int): int {
  gf()
}
