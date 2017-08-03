// RUN: %dafny /print:"%t.print" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Ref<A(0)> {
  var val: A
}

method Nice(n: int) {
  var f : int -> int := x => x;
  var i := new Ref<int>;
  i.val := 0;
  while i.val < n
    invariant forall u :: f.requires(u)
    invariant forall u :: f.reads(u) == {}
    invariant forall u :: f(u) == u + i.val
  {
    i.val := i.val + 1;
    f := x => f(x) + 1;
  }
}


method OneShot(n: int) {
  var f : int -> int := x => x;
  var i := 0;
  while i < n
    invariant forall u :: f.requires(u)
    invariant forall u :: f(u) == u + i
  {
    i := i + 1;
    f := x requires f.requires(x) reads f.reads(x) => f(x) + 1;
  }
}

method HeapQuant(n: int) {
  var f : int -> int := x => x;
  var i := new Ref;
  ghost var r := 0;
  i.val := 0;
  while i.val < n
    invariant forall u :: f.requires(u)
    invariant forall u :: f.reads(u) == {}
    invariant r == i.val
    invariant forall u :: f(u) == u + r
  {
    i.val, r := i.val + 1, r + 1;
    f := x => f(x) + 1;
  }
}

