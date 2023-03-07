// RUN: %exits-with 0 %resolve "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module A {
  module B
}

// Checks for warning if there is no companion external module
