module A {
  module B {
    module C {
    }
    module D {
      import X =C
    }
  }
}

module D {
  import A.B.C
}
