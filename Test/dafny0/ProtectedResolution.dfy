// RUN: %dafny /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module J0 {
  function F0(): int
  protected function F1(): int
  predicate R0()
  protected predicate R1()
}
module J1 refines J0 {
  protected function F0(): int  // error: cannot add 'protected' modifier
  function F1(): int  // error: cannot drop 'protected' modifier
  protected predicate R0()  // error: cannot add 'protected' modifier
  predicate R1()  // error: cannot drop 'protected' modifier
}

module M0 {
  function F(): int { 5 }
  protected function G(): int { 5 }
  predicate P() { true }
  protected predicate Q() { true }
}
module M1 refines M0 {
  function F... { 7 }  // error: not allowed to change body
  protected function G... { 7 }  // error: not allowed to change body
  predicate P... { true }  // error: not allowed to extend body
  protected predicate Q... { true }  // fine
}

module Y0 {
  protected function {:opaque} F(): int { 5 }  // error: protected and opaque are incompatible
}
