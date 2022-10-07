// RUN: %dafny_0 -compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class C {
  const a := b + b
  const b: int

  constructor (x: int) {
    var k := a;
    print a, "\n";
    b := x;
    assert k == a;
    print a, "\n";
    if k != a {
      var y := 5 / 0; // this can crash
    }
  }
}

class D {
  const a: int := b
  const b: int

  constructor () {
    b := a + 1;
    new;
    assert false;
  }
}

method Main() {
  var c := new C(5);
  var d := new D();
}