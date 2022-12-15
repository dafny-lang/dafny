// RUN: %exits-with 4 %dafny /allocated:2 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class C {
  constructor ()
    ensures fresh(this)
    ensures !old(allocated(this)) && allocated(this)
  {
  }
  constructor NotGood()
    // the following was once provable under /allocated:2
    ensures false  // error
  {
  }
  method M()
  {
  }
}

method Main() {
  var c := new C();
  assert fresh(c);
  assert allocated(c) && !old(allocated(c));
  c.M();
}
