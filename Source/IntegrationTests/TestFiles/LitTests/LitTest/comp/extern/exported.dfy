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

  method {:extern} GetX() returns (r: int) {
    r := x;
  }

  function {:extern} AddY(r: int): int {
    r + y
  }

  static function {:extern} AddOne(r: int): int {
    r + 1
  }
}

method Main() {
  var foo := Foo.Builder(3, 2);
  var x := foo.GetX(); 
  print Foo.AddOne(Foo.AddY(x));
}