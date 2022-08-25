---
title: I can define a trait with some type parameters say trait Test<A, B, C>. When I use this trait is there a way to get Dafny to infer these types for me?
---

## Question

I can define a trait with some type parameters say trait `Test<A, B, C>`. When I use this trait is there a way to get Dafny to infer these types for me?

## Answer

Type inference, though quite extensive in its effect, only works within the bodies of functions and methods.
Types in signatures and actual values for type parameters need to be written explicitly.

When type inference is used (within a body), types are determined by how they are used, not just be initializing
expressions. So the inferred type in a declaration may depend on code that appears textually after the declaration.
Here is some example code:
```dafny
class C<X(0)> {
  static method M() returns (x: X) {
  }

  method P() {
    var x0 := M();        // type of x0 inferred to be X, from M()'s signature
    var x1 := C<int>.M(); // type of x1 inferred to be int
    var x2: int := C.M(); // M() instantiated with int

    var x3 := C.M();      // error: type of x3 is underspecified
    var x4: int := M();   // error: M() instantiated with X, but x4 has type int
  }
}
```
