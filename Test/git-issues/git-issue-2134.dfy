// RUN: %exits-with 2 %dafny /typeSystemRefresh:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module NewtypeCycle0 {
  newtype A = b | P(b) // error: cycle in definition
  newtype B = a: A | true

  predicate P(b: B)
}

module NewtypeCycle1 {
  newtype A = b | P(b) // error: cycle in definition
  newtype B = a | Q(a)

  predicate P(b: B)
  predicate Q(a: A)
}

module NewtypeCycle2 {
  newtype B = b | P(b) // error: cycle in definition

  predicate P(b: B)
}

module NewtypeCycle3 {
  newtype B = b | b == X // error: cycle in definition
  const X: B
}

module NewtypeCycle4 {
  newtype B = b | b == X() // error: cycle in definition
  function X(): B
}

// ------------------------------

module SubsetTypeCycle0 {
  type A = b | P(b) // error: cycle in definition
  type B = a: A | true

  predicate P(b: B)
}

module SubsetTypeCycle1 {
  type A = b | P(b) // error: cycle in definition
  type B = a | Q(a)

  predicate P(b: B)
  predicate Q(a: A)
}

module SubsetTypeCycle2 {
  type B = b | P(b) // error: cycle in definition

  predicate P(b: B)
}

module SubsetTypeCycle3 {
  type B = b | b == X // error: cycle in definition
  const X: B
}

module SubsetTypeCycle4 {
  type B = b | b == X() // error: cycle in definition
  function X(): B
}

