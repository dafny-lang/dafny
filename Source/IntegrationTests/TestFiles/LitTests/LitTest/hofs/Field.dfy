// RUN: %testDafnyForEachResolver --expect-exit-code=4 "%s"


// calling fields should not make a resolution error:

class Ref<A(0)> {
  var val: A
}

method Nope() {
  var f := new Ref<int --> bool>;
  assert f.val(0);  // error: precondition and assert
}

class FnRef<A(0),B(0)> {
  var fn: A --> B
}

method Nope2() {
  var f := new FnRef<int,bool>;
  assert f.fn(0);  // error: precondition and assert
}
