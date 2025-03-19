// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"


module Class {
  class T {
    static const a := 1 + b
    static const b := 2

    static ghost predicate F() decreases 0 { !L() }
    static least predicate L() { F() }
      // a recursive call from a least predicate can go only to other least predicates

    static least predicate Negative() { !Negative() }
      // a least predicate can be called recursively only in positive positions
    static least predicate Ensures() ensures false { Ensures() }
      // a least predicate is not allowed to declare any ensures clause
  }

  method Oops0() ensures false { var _ := T.Ensures(); }
  method Oops1() ensures false { var _ := T.a; }
  method Oops2() ensures false { var _ := T.F(); }
  method Oops3() ensures false { var _ := T.Negative(); }
}

module Datatype {
  datatype T = A {
    static const a := 1 + b
    static const b := 2

    static ghost predicate F() decreases 0 { !L() }
    static least predicate L() { F() }
      // a recursive call from a least predicate can go only to other least predicates

    static least predicate Negative() { !Negative() }
      // a least predicate can be called recursively only in positive positions
    static least predicate Ensures() ensures false { Ensures() }
      // a least predicate is not allowed to declare any ensures clause
  }

  method Oops0() ensures false { var _ := T.Ensures(); }
  method Oops1() ensures false { var _ := T.a; }
  method Oops2() ensures false { var _ := T.F(); }
  method Oops3() ensures false { var _ := T.Negative(); }
}

module Newtype {
  newtype T = int {
    static const a := 1 + b
    static const b := 2

    static ghost predicate F() decreases 0 { !L() }
    static least predicate L() { F() }
      // a recursive call from a least predicate can go only to other least predicates

    static least predicate Negative() { !Negative() }
      // a least predicate can be called recursively only in positive positions
    static least predicate Ensures() ensures false { Ensures() }
      // a least predicate is not allowed to declare any ensures clause
  }

  method Oops0() ensures false { var _ := T.Ensures(); }
  method Oops1() ensures false { var _ := T.a; }
  method Oops2() ensures false { var _ := T.F(); }
  method Oops3() ensures false { var _ := T.Negative(); }
}

module AbstractType {
  type T {
    static const a := 1 + b
    static const b := 2

    static ghost predicate F() decreases 0 { !L() }
    static least predicate L() { F() }
      // a recursive call from a least predicate can go only to other least predicates

    static least predicate Negative() { !Negative() }
      // a least predicate can be called recursively only in positive positions
    static least predicate Ensures() ensures false { Ensures() }
      // a least predicate is not allowed to declare any ensures clause
  }

  method Oops0() ensures false { var _ := T.Ensures(); }
  method Oops1() ensures false { var _ := T.a; }
  method Oops2() ensures false { var _ := T.F(); }
  method Oops3() ensures false { var _ := T.Negative(); }
}

module Cycles {
  class Class {
    static const a := 1 + b // const definition contains a cycle: a -> b -> a
    static const b := 2 + a
  }
  datatype Datatype = A {
    static const a := 1 + b // const definition contains a cycle: a -> b -> a
    static const b := 2 + a
  }
  newtype Newtype = int {
    static const a := 1 + b // const definition contains a cycle: a -> b -> a
    static const b := 2 + a
  }
  type AbstractType {
    static const a := 1 + b // const definition contains a cycle: a -> b -> a
    static const b := 2 + a
  }
}
