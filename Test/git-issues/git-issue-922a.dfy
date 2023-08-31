// RUN: %exits-with 4 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module FOO {
  /** Another type definition. */
  datatype O = O(x: nat)

  /** This should not be allowed. */
  const OO := O(-1)   // error: argument is not a nat

}
