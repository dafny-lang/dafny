// RUN: %exits-with 2 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module A {
  export TR reveals T
  export TO provides T

  export TTR reveals TT
  export TTO provides TT

  type T = bool
  type TT = int
}

module B {
  import A`{TR,TTR}

  method Test() {
    var at : A.T;
    var att : A.TT;

    var e := at == false;
    var f := att == 1;
  }
}

module C {
  import A`{TR,TO}

  method Test() {
    var at : A.T;
    var att : A.TT; // error

    var e := at == false;
  }
}

module D {
  import A`{TO,TTO}

  method Test() {
    var at : A.T;
    var att : A.TT;

    var e := at == false; // error
    var f := att == 1; // error
  }


}
