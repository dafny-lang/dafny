// RUN: %exits-with 2 %resolve "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module A {
  module B
}

module X

// Checks that a top-level body-less module delcl is bad, but one in a module is OK
