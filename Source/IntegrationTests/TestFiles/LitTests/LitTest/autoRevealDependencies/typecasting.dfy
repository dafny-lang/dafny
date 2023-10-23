// RUN: %baredafny verify %args --default-function-opacity autoRevealDependencies "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module M {
  function one() : (r:int) {
  
    1
  }

  datatype Test = | Int(i:int)
  {
    predicate Nat() {
      match this
        case Int(i) => i >= 0
    }
  }

  type Test_Nat = e:Test | e.Nat() witness Int(0)
}

module N {
  import opened M

  function two() : (r: Test_Nat)
    ensures r.i == 2 
  {
    Int( Int(one() + one()).i )
  }
}