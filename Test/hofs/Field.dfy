// RUN: %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// calling fields should not make a resolution error:

class Ref<A> {
  var val: A;
}

method Nope() {
  var f := new Ref<int -> bool>;
  assert f.val(0);
}

class FnRef<A,B> {
  var fn: A -> B;
}

method Nope2() {
  var f := new FnRef<int,bool>;
  assert f.fn(0);
}

