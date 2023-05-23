// RUN: %exits-with 4 %dafny /print:"%t.print" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function Const<A,B>(a : A) : B -> A {
  b => a
}

method Main() {
  assert (a => b => a) == (u : int) => (v : int) => u;
  if * {
    assert Const == (u : int) => (v : int) => u;  // wish
  } else if * {
    assert Const<int,int> == (u : int) => (v : int) => u;  // wish
  } else if * {
    assert Const<int,int> == u => v => u;  // wish
  } else {
    var f := Const<int,int>;
    var g := u => v => u;
    assert f == g;  // wish
  }
}
