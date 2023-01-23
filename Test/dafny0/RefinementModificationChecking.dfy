// RUN: %exits-with 2 %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

abstract module R1 {
  class HappyBay {
    var f: int;
    method m(y: set<int>) returns (r: int)
      modifies this;
    {
      var t := y;
    }
  }
}

module R2 refines R1 {
  class HappyBay ... {
    var g: nat;
    method m ...
    {
      ...;
      var x := 3;
      t := {1}; // error: previous local
      r := 3; // error: out parameter
      f := 4; // error: previously defined field
      x := 6; // fine: new local
      g := 34;// fine: new field
    }
  }
}

abstract module M0 {
  class C {
    method Init()
      modifies this;
    { }
    method InitWithSideEffects(c: C)
      modifies c;
    { }
    method mmm(arr: array<int>) {
      var a: C :| true;
      var b: C :| true;
    }
  }
}

module M1 refines M0 {
  class C ... {
    method mmm... {
      var a := new C;  // fine
      var b := new C.Init();  // fine
      var c := new C.InitWithSideEffects(b);  // error: modifies previous state
      if 12 < arr.Length {
        arr[12] := 26;  // error: modifies previously defined state
      }
    }
  }
}
