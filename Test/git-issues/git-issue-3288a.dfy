// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t" 

// Check that contextual keywords can be used as identifiers

const least := 0
const greatest := 42
const to := true
const downto := false
const older := 0.0

module M {
  function least(): int { 42 }
  method greatest() {}
  type to
  predicate downto() { true }
  module older {}
}
