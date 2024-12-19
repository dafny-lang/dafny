// RUN: %exits-with 2 %verify --type-system-refresh=false --general-newtypes=false "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module AM {

  method M0(d: int)
  {
    var a := new int[25](_ => d);
    assert a.Length == 25;
    assert a[18] == d;
  }

  method M1()
  {
    var f := (r: real) => r;
    var a := new real[25](f);  // error: initializer has incorrect type
    assert a.Length == 25;
    assert a[18] == 18.0;
  }

  method M2<D>(d: D)
  {
    var a := new D[25](d);  // error: initializer has incorrect type (error message includes a hint)
    assert a.Length == 25;
    assert a[18] == d;
  }

  method M3<D>(d: D)
  {
    var g := (_: int) => d;
    var a := new D[25](g);
    assert a.Length == 25;
    assert a[18] == d;
  }

  method M4(d: char)
  {
    var a := new char[25,10,100]((x:int) => d);  // error: wrong type
    assert a.Length0 == 25;
    assert a.Length1 == 10;
    assert a.Length2 == 100;
    assert a[18,3,23] == d;
  }

  method M5(d: char)
  {
    var a := new char[25,10]((x, y) => if x==y then '=' else d);
    assert a.Length0 == 25;
    assert a.Length1 == 10;
    assert a[18,3] == d;
  }

  method M6<D>(d: D)
  {
    var a := new D[1,2,4,8,16](d);  // error: initializer has incorrect type (error message includes a hint)
    assert a.Length3 == 8;
    assert a[0,0,0,0,0] == d;
  }
}

module BM {
  ghost function GhostF(x: int): char { 'D' }
  method M(n: nat) returns (a: array<char>) {
    a := new char[n](GhostF);  // error: use of ghost function not allowed here
    if 5 < n {
      assert a[5] == 'D';
    }
  }
}

// ------- initializing display --------------------------------------

module CM {
  newtype int32 = x | -0x8000_0000 <= x < 0x8000_0000

  method Display0<D>(d: D, n: int)
  {
    var a := new nat[4] [100, 75, 50, 25];
    var b := new int32[4] [100, 75, n, 25];  // error: "n" has type "int", not "int32"
  }
}

module DM {
  method Ghost(ghost g: int)
  { var a;
    a := new int[4] [100, 75, g, 25];  // error: "g" is ghost
  }
}

// ------- optional syntactic parts --------------------------------------

module EM {
  class C {}
  class D {}
  method M() {
    var a := new [3] [2, 5, 8];
    var b := new [1][1];
    a, b := b, a;  // a and b have the same type, array<int>
    var c := new [2] [false, 'f'];  // error: type inference fails
    var xc, xd := new C, new D;
    var d := new [2] [ xc, xd ];
    var e: array<object>;
    d, e := e, d;  // d and e have the same type, array<object>
    var f := new [3](i => i as real);
    var g: array<char> := new [10];
  }
}

module EM' {  // same as EM, but with sizes left out (where allowed)
  class C {}
  class D {}
  method M() {
    var a := new [] [2, 5, 8];
    var b := new [][1];
    a, b := b, a;  // a and b have the same type, array<int>
    var c := new [] [false, 'f'];  // error: type inference fails
    var xc, xd := new C, new D;
    var d := new [] [ xc, xd ];
    var e: array<object>;
    d, e := e, d;  // d and e have the same type, array<object>
  }
}

module FM {
  method M() {
    var a := new [0];  // error: underspecified array-element type
  }
}
