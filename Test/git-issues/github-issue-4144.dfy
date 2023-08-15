// RUN: %baredafny verify %args %s > %t
// RUN: %diff "%s.expect" "%t"

module P {
  predicate m() reads {}
  predicate p() reads []
  predicate q() reads multiset{}
  
  predicate k(o: object) reads (() => {o})
  predicate l(o: object) reads ((x: int) => [o])
  predicate n(o: object) reads ((y: real, z: real) => multiset{o})

  predicate k'() reads (() => {})
  predicate l'() reads ((x: int) => [])
  predicate n'() reads ((y: real, z: real) => multiset{})
} 

module Q refines P {
  predicate m() { true }
  predicate p() { true }
  predicate q() { true }
  
  predicate k(o: object) { true }
  predicate l(o: object) { true }
  predicate n(o: object) { true }

  predicate k'() { true }
  predicate l'() { true }
  predicate n'() { true }
}

module EmptySet {
    predicate m()
      reads {}
    {
      m'({}, 0)
    }
    
    predicate m'(s: set<object?>, j: nat)
      reads {}
      decreases s, j // note, explicit decreases clause
    {
      if s == {} then true else m()
    }
}