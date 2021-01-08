// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module FOO {
  // seq with more than one element
  type L = x : seq<int> | |x| >= 1 as int witness [1]

  // a datatype using the previous type
  datatype D = D( xl : L)

  /** This const should not be allowed.  */
   const KK := D([])    // label: FaultyConstDef

  method m(i: int, j: int) {
    var KKK := D([]);
  }
}
