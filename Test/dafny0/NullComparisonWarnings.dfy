// RUN: %baredafny run %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  print "despite the warnings, the program still compiles\n";
  var c := new MyClass();
  M(c, c, 0, {});
}

class MyClass {
  var next: MyClass

  constructor () {
    next := this;
  }
}

method M(x: MyClass, c: MyClass, N: nat, S: set<MyClass>) {
  var y: MyClass := new MyClass();
  var n: nat := N;
  while n != 0 {
    y := new MyClass();
    n := n - 1;
  }

  var b;
  b := x == null;  // warning (with hint)
  b := y == null;  // warning (with hint)
  b := c.next == null;  // warning (with hint)
  b := x != null;  // warning (with hint)
  b := y != null;  // warning (with hint)
  b := c.next != null;  // warning (with hint)

  b := null == x;
  b := x == (null);  // no warning (this could easily be changed in the implementation, but I left it as a kind of "nowarn" feature)

  b := null in S;  // warning
  b := null !in S;  // warning

  b := forall u: MyClass :: u in S ==> u != null;  // warning

  var c0: Cell<MyClass?> := new Cell<MyClass?>(c);
  var c1: Cell<MyClass> := new Cell<MyClass>(c);
  b := null != c0.data;
  b := null != c1.data;  // warning (no hint)
}

class Cell<G> {
  var data: G
  constructor (g: G) {
    data := g;
  }
}
