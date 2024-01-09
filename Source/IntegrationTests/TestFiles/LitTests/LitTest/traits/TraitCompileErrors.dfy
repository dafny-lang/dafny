// RUN: %exits-with 3 %dafny /print:"%t.print" /dprint:"%t.dprint" "%s" /allowAxioms:0 > "%t"
// RUN: %diff "%s.expect" "%t"

module StaticMembers {
  trait Tr {
    // the following static members must also be given bodies, but that's checked by the compiler
<<<<<<< HEAD:Test/traits/TraitCompileErrors.dfy
    static function method Func(): int ensures false
    static method Method() ensures false
    static twostate function TwoF(): int ensures false
    static twostate lemma TwoL() ensures false
=======
    static ghost function Func(): int
    static method Method()
    static twostate function TwoF(): int
    static twostate lemma TwoL()
>>>>>>> origin/master:Source/IntegrationTests/TestFiles/LitTests/LitTest/traits/TraitCompileErrors.dfy
    static least predicate P()
    static greatest predicate Q()
    static least lemma IL() ensures false
    static greatest lemma CL() ensures false
  }
}
