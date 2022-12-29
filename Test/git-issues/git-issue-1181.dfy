// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type T {
  predicate P(t: T)
  predicate Q()
    requires P(this)  // once got the bogus "type mismatch for argument (function expects T, got T)"
}
