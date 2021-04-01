// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function F(i: int): int

method M() {
  ghost var f := old(i => F(i));  // the translation of this once had crashed the verifier
}

class MyClass {
  var y: int

  method N()
    modifies this
  {
    y := 8;
    label L:
    var p := new MyClass;
    label K:
    if * {
      ghost var g := old@L((x: int) reads p.R(this) => x);  // error, because p is not allocated in L
    } else if * {
      ghost var g := old@L((x: int) reads R(p) => x);  // error, because p is not allocated in L
    } else if * {
      ghost var g := old@K((x: int) reads p.R(p) => x);
    } else {
      ghost var g := old((x: int) reads p.R(p) => x);  // error, because p is not allocated in old state
    }
  }

  function R(c: MyClass): MyClass
    reads this
  {
    this
  }
}
