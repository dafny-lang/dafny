// RUN: %testDafnyForEachCompiler "%s"

trait MyTrait<T> {
  method Bar(ghost x: T, y: T) returns (z: T)
}

class MyClass extends MyTrait<int> {
  constructor() {}
  method Bar(ghost x: int, y: int) returns (z: int) {
    return y;
  }
}

method Main() {
  var c := new MyClass();
  var z := c.Bar(7, 42);
  expect z == 42;
}