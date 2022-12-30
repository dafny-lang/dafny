// RUN: %baredafny verify %args --print-tooltips "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This file checks that function applications yield trigger candidates

method M(P: (int -> int) -> bool, g: int -> int)
  requires P.requires(g)
  requires P(g) {
  assume forall f: int -> int :: P.requires(f);
  assume forall f: int -> int :: P(f) ==> f.requires(10) && f(10) == 0;
  assert forall f: int -> int ::
    (forall x :: f.requires(x) && g.requires(x) ==> f(x) == g(x)) ==>
    f.requires(10) ==>
    f(10) == 0;
}
