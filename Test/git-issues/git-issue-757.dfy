// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module M {
  export
    provides A, A.New
  datatype A<T> = A(s:seq<T>) {
    static method New() returns (self: A<T>) {
      self := A([]);
    }
  }
}

module M2 {
  import M

  method test() {
    var a := M.A<int>.New(); // Used to throw when resolving this line
  }
}

