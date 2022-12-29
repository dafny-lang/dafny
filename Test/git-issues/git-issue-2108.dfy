// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module M0.M1.Base {}

module M0.M2 {
  import M1.Base

  module Derived refines Base {
  }
}
