// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"


// Test that the export-provided type `T` is not recognized as a reference type in Client.

module FarAway {
  export
    provides T
    reveals U
    reveals M
  export Everything extends FarAway
    reveals T

  type T(==) = object
  type U = T

  type M = real -> set<T>
}

module Client {
  import FarAway

  function F(t: FarAway.U): int
    reads t // error: type of t is not known to be allowed in reads claues

  function G(s: set<FarAway.U>): int
    reads s // error: type of s is not known to be allowed in reads claues

  function H(f: real -> set<FarAway.U>): int
    reads f // error: type of f is not known to be allowed in reads claues

  function K(m: FarAway.M): int
    reads m // error: type of m is not known to be allowed in reads claues
}

module CloseClient {
  import FarAway`Everything

  function F(t: FarAway.U): int
    reads t

  function G(s: set<FarAway.U>): int
    reads s

  function H(f: real -> set<FarAway.U>): int
    reads f

  function K(m: FarAway.M): int
    reads m
}
