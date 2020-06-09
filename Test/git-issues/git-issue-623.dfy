// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module M1 {
  export Abs provides m, T
  export Conc provides m, MyClass reveals T

  class MyClass {

  }

  type T = MyClass

  lemma m(f : T ~> bool)
    requires forall t :: f.requires(t) ==> f(t)
    { }

}

module M2 {
  import M1`Abs

  method k(t : M1.T){

  }
}

