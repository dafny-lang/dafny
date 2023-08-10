// RUN: %exits-with 2 %dafny /typeSystemRefresh:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module NewtypeCycle0 {
  newtype A = b | P(b)
  newtype B = a: A | true

  predicate P(b: B) // error: cycle in definition
}

module NewtypeCycle1 {
  newtype A = b | P(b)
  newtype B = a | Q(a)

  predicate P(b: B) // error: cycle in definition
  predicate Q(a: A)
}

module NewtypeCycle2 {
  newtype B = b | P(b)

  predicate P(b: B) // error: cycle in definition
}

module NewtypeCycle3 {
  newtype B = b | b == X
  const X: B // error: cycle in definition
}

module NewtypeCycle4 {
  newtype B = b | b == X() // error: cycle in definition
  function X(): B // error: cycle in definition
}

// ------------------------------

module SubsetTypeCycle0 {
  type A = b | P(b)
  type B = a: A | true

  predicate P(b: B) // error: cycle in definition
}

module SubsetTypeCycle1 {
  type A = b | P(b)
  type B = a | Q(a)

  predicate P(b: B) // error: cycle in definition
  predicate Q(a: A)
}

module SubsetTypeCycle2 {
  type B = b | P(b)

  predicate P(b: B) // error: cycle in definition
}

module SubsetTypeCycle3 {
  type B = b | b == X
  const X: B // error: cycle in definition
}

module SubsetTypeCycle4 {
  type B = b | b == X() // error: cycle in definition
  function X(): B // error: cycle in definition
}

