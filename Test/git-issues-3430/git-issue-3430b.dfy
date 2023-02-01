// RUN: %baredafny resolve --use-basename-for-filename "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module A {
  module A.B
}
