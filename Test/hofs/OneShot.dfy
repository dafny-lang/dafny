// RUN: %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Ref<A(0)> {
  var val : A;
}

method OneShot() {
  var g : () -> bool;
  var i : Ref<int>;
  i := new Ref;

  g := () reads i -> true;  // using a (deprecated) one-shot arrow here means "g" acquires
                           // a precondition that says it can only be applied in this heap
  assert g();

  i.val := i.val + 1; // heap changes

  if * {
    assert g();         // error: precondition violation
  } else {
    assert !g();        // error: precondition violation
  }
}
