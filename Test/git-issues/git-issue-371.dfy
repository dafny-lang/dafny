// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module M {
  type TT = int
}

module MN {
  export reveals TN
  type TN = int
  type TKN = int
}

module ME {
  export E reveals TE
  export K reveals TK
  type TE = int
  type TK = int
}

module MA {
  module Inner {
    type T17 = x | 0 <= x < 17
  }
}

module MB {
  module I {
    export Z provides T42 reveals T42
    export Z3 provides T43 reveals T43
    type T42 = x | 0 <= x < 42
    type T43 = x | 0 <= x < 43
  } 
}

module MC {
  export Y provides TMB, K reveals TMB
  type TMB = x | 0 <= x < 13
  module K {
    type T42 = x | 0 <= x < 42
  } 
}

//import M  // Error
//import ME // Error
//import MN // Error
//import ME`E // Error

module A {

  import TTT = M
  import TTE = ME`E

  import M
  import ME`E
  import MN

  import MA
  import MAI = MA.Inner
  import MA.Inner
  import MB
  import MB.I`Z
  import II = MB.I // This should be an error
  import YY = MC`Y

  class ZZ {
    constructor() { yyy := 4; a := 5; }
/*
    var t: TTT.TT;
    var te: TTE.TE;
    var m: M.TT;
    var me: ME.TE;
    //var mf: ME.TK; // Error
    var mn: MN.TN;
    //var mk: MN.TKN; // Error

    var zx: MAI.T17;
    var zz: Inner.T17;
*/
    var za: I.T42;
    var zb: I.T43; // Error
    var zc: II.T42;

    //var yy: I.T42;
    var yyy: YY.TMB;
    var a: YY.K.T42;
  }

}

module B0 {
  import ME
  class Z {
    var a: ME.TE; // is an Error??
    var b: ME.TK; // is an Error??
  }
}

module B1 {
  import ME`E
  class Z {
    var a: ME.TE;
    var b: ME.TK; // Error
  }
}

module B2 {
  import ME`{E,K}
  class Z {
    var a: ME.TE;
    var b: ME.TK;
  }
}

module B3 {
  import ME = ME`E
  import MK = ME`K
  class Z {
    var a: ME.TE;
    var b: MK.TK;
    var c: ME.TK; // Error
  }
}

module B4 {
  import ME; // Should be an error
  import MA.Inner  // currently disallowed, but I think it should be allowed
  class ZZ {
  var zz: Inner.T17;
}
