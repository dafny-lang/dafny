// RUN: %baredafny run %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Enum = One | Two | Three {
  predicate method Even() {
    this.Two?
  }

  predicate method Even'() {
    match this
      case One | Three => false
      case Two => true
  }

  predicate method Even''() {
    match this
      case Two => true
      case One | Three => false
  }

  lemma EvenOk() ensures Even() == Even'() == Even''() {}
}

module Constants {
  const ONE := 1
  const TWO := 2

  method M(i: int) {
    match i
      case | ONE | TWO => return; // `ONE` and `TWO` are not variables here
      case | _ => // Not redundant
  }
}

module Lists {
  datatype List<T> = Nil | Cons(car: T, cdr: List<T>) {
    function {:fuel 5} Length(): nat {
      match this
        case Nil => 0
        case Cons(_, t) => 1 + t.Length()
    }
  }

  predicate method ContainsOne(l: List<int>)
    requires l.Length() == 3
  {
    l.car == 1 || l.cdr.car == 1 || l.cdr.cdr.car == 1
  }

  predicate method ContainsOne'(l: List<int>)
    requires l.Length() == 3
  {
    match l
      case Cons(1, Cons(_, Cons(_, Nil)))
         | Cons(_, Cons(1, Cons(_, Nil)))
         | Cons(_, Cons(_, Cons(1, Nil))) =>
       true
      case Cons(_, Cons(_, Cons(_, Nil))) =>
        false
  }

  lemma ContainsOneOK(l: List<int>)
    requires l.Length() == 3
    ensures ContainsOne(l) == ContainsOne'(l)
  {}
}

import opened Lists

module TestVariables {
  datatype DT = A | B | C

  method M(dt: DT) returns (j: int) {
    match dt {
      case C => return 0;
      case A | B => var x := (y => y)(1); assert x == 1;
        return x;
    }
  }

  method M2(dt: DT) returns (j: int) {
    match dt {
      case C => return 0;
      case _ => var x := (y => y)(1); assert x == 1;
        return x;
    }
  }

  function method F(dt: DT): int {
    match dt {
      case C => 0
      case A | B => var x := (y => y)(1); assert x == 1; x
    }
  }
  function method F2(dt: DT): int {
    match dt {
      case C => 0
      case _ => var x := (y => y)(1); assert x == 1; x
    }
  }
}
import opened TestVariables

method Main() {
  expect One.Even() == One.Even'() == One.Even''() == false;
  expect Two.Even() == Two.Even'() == Two.Even''() == true;
  expect Three.Even() == Three.Even'() == Three.Even''() == false;

  var a0 := Cons(0, Cons(0, Cons(0, Nil)));
  expect ContainsOne(a0) == ContainsOne'(a0) == false;
  var a1 := Cons(1, Cons(0, Cons(0, Nil)));
  expect ContainsOne(a1) == ContainsOne'(a1) == true;
  var a2 := Cons(0, Cons(1, Cons(0, Nil)));
  expect ContainsOne(a2) == ContainsOne'(a2) == true;
  var a3 := Cons(0, Cons(0, Cons(1, Nil)));
  expect ContainsOne(a3) == ContainsOne'(a3) == true;
  
  var b0 := M(A);
  var b1 := M(B);
  var b2 := M2(A);
  var b3 := M2(B);
  var b4 := F(A);
  var b5 := F(B);
  var b6 := F2(A);
  var b7 := F2(B);
  expect 1 == b0 == b1 == b2 == b3 == b4 == b5 == b6 == b7;
  
  print "OK\n";
}
