// RUN: %exits-with 4 %baredafny verify %args --print-tooltips "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This tests shows that, since quantifiers are split, it becomes possible to know more precisely what part of a precondition did not hold at the call site.

method f()
  requires forall y :: y > 0 && y < 0 {
}

method g(x: int) {
  f();
}

function gf(): int
  requires forall y :: y > 0 && y < 0 {
    1
}

function gg(x: int): int {
  gf()
}
