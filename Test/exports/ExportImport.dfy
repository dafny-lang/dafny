// RUN: %exits-with 2 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module A {
  export AO provides T
  export AR reveals T

  type T = bool
}

module B {
  export BO provides TT, BAO
  export B provides TT
  export BR provides BAR reveals TT

  type TT = BAR.T

  import BAO = A`AO
  import BAR = A`AR

  method Test() {
     var tt : TT;
     var aot : BAO.T;
     var aor : BAR.T;

     var e := tt == aot;
     var f := aot == aor;
     var g := tt == false;
  }

}

module C {
  import CAO = B.BAO // error - BAO not in B`B
}

module CC {
  import B
  import CCAO = B.BAO // error, not in default set
}

module D {
  import B`BO
  import DAO = B.BAO

  method Test() {
    var daot : DAO.T;
    var e := daot == false; // error

    var btt : B.TT;
    var f := daot == btt; // error
  }
}

module DD {
  import B`BR
  import DAR = B.BAR

  method Test() {
    var daot : DAR.T;
    var e := daot == false;

    var btt : B.TT;
    var f := daot == btt;
  }
}


