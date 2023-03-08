// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type T {
  ghost predicate P(t: T)
  ghost predicate Q()
    requires P(this)  // once got the bogus "type mismatch for argument (function expects T, got T)"
}
