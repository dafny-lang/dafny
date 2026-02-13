// RUN: %testDafnyForEachCompiler "%s" -- --type-system-refresh=true --general-newtypes=true


method Main() {
  Members.Test();
}

module Members {
  method Test() {
    TestConst();
    var b := TestFunction();
    b.PrintMe();
    TestBoolBool(true);
    Int.P(b);
    (5.98 as Real).M();
    (2.98 as TooReal).M();
    (65 as Bv).M();
    Map.Test();
  }

  method TestConst() {
    var b: Bool := true;
    assert b;
    assert b.n == 4;
    print b, " ", b.n, "\n"; // true 4
  }

  method TestFunction() returns (b: Bool) {
    b := true;
    var x := b.F();
    assert x == 15;
    assert b.H(300) == 1;
    print b, " ", x, " ", b.H(300), "\n"; // true 15 1
  }
  
  newtype Bool = bool {
    const n: int := match this case false => 3 case _ => 4
    function F(): int {
      if this then 15 else 8
    }
    function H(x: int): int {
      1
    }
    method PrintMe() {
      print this, " ", F(), " ", n, "\n"; // true 15 4
    }
  }

  newtype BoolBool = b: Bool | true {
    function G(): int {
      if this then
        var b: Bool := this as Bool;
        assert b;
        if b then
          var bb := b as bool;
          assert bb;
          9
        else
          -1 // we never get here
      else
        var b: Bool := this as Bool;
        var bb: bool := this as bool;
        assert !b;
        assert !bb;
        8
    }
  }

  method TestBoolBool(bb: BoolBool) {
    var a := bb.G();
    assert bb ==> a == 9;
    assert !bb ==> a == bb.F();
    var x0 := bb.F();
    var x1 := (bb as Bool).F();
    print a, " ", x0, " ", x1, "\n"; // 9 15 15
  }

  newtype Int = int {
    static method P<X>(x: X) {
      print "Int.P: ", x, "\n"; // Int.P true
    }
  }

  newtype Real = real {
    method M() {
      var a := Floor;
      var b := this.Floor;
      var c := (this as real).Floor;
      var d := RealFloor();
      assert a == b == c == d;
      print a, " ", b, " ", c, " ", d, "\n"; // 5 5 5 5
    }

    function RealFloor(): int {
      Floor
    }
  }
  
  newtype TooReal = r: real | 2.7 <= r < 3.14 witness 3.000 {
    method M() {
      var a := Floor;
      var b := this.Floor;
      var c := (this as real).Floor;
      assert a == b == c;
      var d: TooReal := *;
      print a, " ", b, " ", c, " ", d, "\n"; // 2 2 2 3.0
    }
  }
  
  newtype Bv = x: bv7 | true {
    method M()
      requires this == 65
    {
      var a := RotateLeft(2);
      var b := this.RotateRight(1);
      var c := (this as bv7).RotateRight(0);
      print a, " ", b, " ", c, "\n"; // 6 96 65
    }
  }
  
  newtype Map = map<int, real> {
    const k: set<int> := Keys
    method M() returns (s: set<int>) {
      s := k;
    }

    static method Test() {
      var m0: Map := map[18 := 4.0];
      var m1: Map := map x | 3 <= x < 7 && x % 2 == 0 :: 3 * x := (10 - x) as real; // map[12 := 6.0, 18 := 4.0]
      var s := m0.M();
      m1 := m1 - s;
      print m1, "\n"; // map[12 := 6.0]
    }
  }
}
