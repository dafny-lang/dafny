// RUN: %exits-with 2 %dafny /print:"%t.print" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method FnEqGhost<A>() {
  ghost var f : A -> A -> A;
  ghost var g : A -> (A -> A);
  ghost var h : (A -> A) -> A;
  ghost var b1 := f == g; // type checking should be ok
  ghost var b2 := f == h; // type checking should fail

  ghost var z;
  ghost var b3 := f == z; // unify in progress
  ghost var b4 := g == z; // should now be ok
  ghost var b5 := h == z; // should now fail

  ghost var zz;
  ghost var b6 := h == zz; // unify in progress
  ghost var b7 := g == zz; // should fail
}

ghost function ToObject(): object

ghost function F(): int
  // Regression: the following used resolve, but would then cause malformed Boogie.
  // There's no strong use case for this, so it's better to just forbid it.
  reads ToObject // error: arrow to collection of references is allowed, but no other arrows
