// RUN: %exits-with 2 %dafny /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module M0 {
  function F(): int { 5 }
  predicate P() { true }
}
module M1 refines M0 {
  function F... { 7 }  // error: not allowed to change body
  predicate P... { true }  // error: not allowed to extend body
}
