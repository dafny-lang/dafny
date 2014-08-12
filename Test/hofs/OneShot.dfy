// RUN: %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Ref<A> {
  var val : A;
}

method OneShot() {
  var g : () -> bool;
  var i : Ref<int>;
  i := new Ref;

  g := () -> true;

  assert g();

  i.val := i.val + 1; // heap changes

  if * {
    assert g();         // should fail
  } else {
    assert !g();        // should fail
  }
}

