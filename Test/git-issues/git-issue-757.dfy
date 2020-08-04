module M {
  export
    provides A, A.New
    //reveals A
  datatype A<T> = A(s:seq<T>) {
    static method New() returns (self: A<T>) {
      self := A([]);
    }
  }
}

module M2 {
  import M

  method test() {
    var a := M.A<int>.New(); // throws when adding this line
  }
}

