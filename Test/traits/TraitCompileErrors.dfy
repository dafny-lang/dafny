// RUN: %exits-with 3 %dafny /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module StaticMembers {
  trait Tr {
    // the following static members must also be given bodies, but that's checked by the compiler
    static ghost function Func(): int
    static method Method()
    static twostate function TwoF(): int
    static twostate lemma TwoL()
    static least predicate P()
    static greatest predicate Q()
    static least lemma IL()
    static greatest lemma CL()
  }
}
