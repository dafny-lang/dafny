// RUN: %testDafnyForEachResolver --expect-exit-code=4 "%s"


module FOO {
  /** Another type definition. */
  datatype O = O(x: nat)

  /** This should not be allowed. */
  const OO := O(-1)   // error: argument is not a nat

}
