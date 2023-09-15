// RUN: %testDafnyForEachCompiler "%s" --refresh-exit-code=0

module myclass {
  class MyClass {
    var num: int

    constructor (x: int) {
      num := x;
    }
  }

  method Main() {
    var c_obj := new MyClass(2);
  }
}

