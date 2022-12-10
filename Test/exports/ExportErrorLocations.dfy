// RUN: %exits-with 2 %dafny /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module MyModule {
  // the source locations in the following error message should be on the token
  // indicated in parentheses
  export
    provides F, FunctionG, Y  // error: not a member ("FunctionG")
    provides Undeniable, YourClass.M  // error: not a class ("YourClass")
    provides Datatype.UndefinedFunction  // error: not a member ("UndefinedFunction")
  export Alt
    provides MyClass.SomeMethod, MyClass.UndefinedMethod, MyClass.x  // error: not a member ("UndefinedMethod")
  export Another
    reveals MyClass.SomeMethod  // error: cannot be revealed ("SomeMethod")
    provides Alt  // error: cannot be exported ("Alt")

  type Y
  function F(): Y
  datatype Datatype = Ctor(z: int)
  lemma Undeniable()
    ensures true
  class MyClass {
    var x: int
    method SomeMethod()
  }
}
