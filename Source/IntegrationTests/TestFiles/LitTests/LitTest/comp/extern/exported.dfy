// RUN: %testDafnyForEachCompiler "%s" -- --allow-axioms --allow-external-contracts
predicate Pre(x: int, y: int) {
  x > y
}

class Foo {

  var x: int
  var y: int

  constructor {:extern} (x: int, y: int) 
    requires Pre(x, y)
  {
      this.x := x; 
      this.y := y;
  }

  static method {:extern} Builder(x: int, y: int) returns (result: Foo)
    requires Pre(x, y)
  {
    result := new Foo(x, y);
  }
}

method Main() {
  var foo := Foo.Builder(3, 2);
  print foo.x;
}