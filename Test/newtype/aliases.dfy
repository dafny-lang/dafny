// RUN: %baredafny resolve --use-basename-for-filename %s > %t
// RUN: %diff "%s.expect" %t

module A {
  import B
  newtype VerySpecificInt = x : B.SpecificIntAlias | x == 1 witness 1
}

module B {
  import C
  type SpecificIntAlias = C.SpecificInt
}

module C {
  newtype SpecificInt = x : int | 0 <= x <= 10
}