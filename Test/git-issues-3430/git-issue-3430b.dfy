// RUN: %exits-with 2 %resolve "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module A {
  module A.B
}

// May not have a qualified body-less module decl
