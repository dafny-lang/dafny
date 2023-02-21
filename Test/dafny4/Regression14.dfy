// RUN: %exits-with 2 %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module AAA {
  ghost function Func(): int
  class MyClass { }
  method Get() returns (m: MyClass)
  method M()
  {
    var p := Get();
    var x := p.Func();  // error: Func is not in MyClass (this used to crash)
  }
}

module BBB {
  const D: MyClass?
  method Get() returns (p: MyClass)
  class MyClass { }
  method M() {
    var p := Get();
    while true
      modifies p.D  // error: D is not in MyClass (this used to crash)
    {
    }
  }
}
