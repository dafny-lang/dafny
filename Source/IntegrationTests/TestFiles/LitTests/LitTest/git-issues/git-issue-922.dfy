// RUN: %exits-with 4 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module FOO {
  // seq with more than one element
  type L = x: seq<int> | 1 <= |x| witness [1]

  // a datatype using the previous type
  datatype D = D(xl: L)

  /** This const should not be allowed.  */
  const KK := D([]) // error: argument to D constructor is not an L

  method M() {
    var k := D([]); // error: argument to D constructor is not an L (but this error may be masked by the one in KK)
  }
}

module FOO' {
  // seq with more than one element
  type L = x: seq<int> | 1 <= |x| witness [1]

  // a datatype using the previous type
  datatype D = D(xl: L)

  method M() {
    var k := D([]); // error: argument to D constructor is not an L
  }
}
