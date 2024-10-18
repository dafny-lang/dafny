// RUN: %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

trait Animal {
    function           not_opaque() : ( rv : int)
    function {:opaque} iam_opaque() : ( rv : int) 

    predicate depends_on_not_opaque() 
       ensures  not_opaque() == 42 
    predicate depends_on_iam_opaque() 
       ensures  iam_opaque() == 42 
}

class Cat extends Animal {
    function           not_opaque() : ( rv : int) { 42 } 
    function {:opaque} iam_opaque() : ( rv : int) 
         //ensures rv == 42
         { reveal iam_opaque();  42 } 

    predicate depends_on_not_opaque() 
       ensures not_opaque() == 42 {true}
    predicate depends_on_iam_opaque() 
       ensures iam_opaque() == 42 {reveal iam_opaque(); true}
}

trait T {
  predicate Valid(x: int)
  method MyMethod(x: int) requires Valid(x)
}

class C extends T {
  predicate {:opaque} Valid(x: int) { true }
  method MyMethod(x: int) requires Valid(x) {
  }
}

// The following two types make sure that the override axiom is produced with the correct
// parameters to the CanCall function.

trait TT {
  opaque predicate Valid<Y>(x: int, y: Y)
}

class CC extends TT {
  opaque predicate Valid<Z>(x: int, z: Z) {
    if 0 < x then Valid(x - 1, z) else true
  }
}
