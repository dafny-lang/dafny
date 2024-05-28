// RUN: %exits-with 4 %verify --type-system-refresh --general-newtypes "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Members {
  method Test() {
    TestConst();
    TestFunction();
    TestBoolBool(true);
  }

  method TestConst() {
    var b: Bool := true;
    assert b;
    assert b.n == 4;
    b := false;
    assert b.n == 4; // error
  }

  method TestFunction() {
    var b: Bool := true;
    var x := b.F();
    assert x == 15;
    assert b.H(300) == 1;
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
      print this, " ", F(), " ", n, "\n";
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
    assert bb.F() == (bb as Bool).F();
  }

  newtype BoolBoolBool = b: BoolBool | b witness true {
    lemma YeahItIsTrue()
      ensures F() == 15
    {
    }
  }

  newtype Int = int {
    static method P<X>(x: X) {
      print "Int.P: ", x, "\n";
    }
  }

  newtype Real = real {
    method M() {
      var a := Floor;
      var b := this.Floor;
      var c := (this as real).Floor;
      assert a == b == c;
    }

    function RealFloor(): int {
      Floor
    }

    method Q()
      requires 2.3 <= this < 2.9
    {
      if
      case true =>
        assert this.Floor == 2;
      case true =>
        assert this.RealFloor() == 2;
    }
  }
  
  newtype TooReal = r: real | 2.7 <= r < 3.14 witness 3.000 {
    method M() {
      var a := Floor;
      var b := this.Floor;
      var c := (this as real).Floor;
      assert a == b == c;
    }
  }
  
  newtype Bv = x: bv7 | x != 31 {
    method M() {
      var a := RotateRight(2);
      var b := this.RotateRight(2);
      var c := (this as bv7).RotateRight(2);
      assert a == b == c;
    }
  }
  
  newtype Map = map<int, real> {
    const k: set<int> := Keys
    method M() returns (s: set<int>) {
      s := k;
    }
  }
  
  newtype IMap = m: imap<int, real> | 10.0 !in m.Values {
    method M() returns (r: iset<(int, real)>) {
      r := Items;
      r := this.Items;
      var th := this;
      r := th.Items;
    }
  }

  type MapSubset<Unused, K> = m: map<K, real> | true
  newtype NewMapSubset = m: MapSubset<bv18, int> | true {
    method M() {
     var s := Keys;
     var t := this.Keys;
     assert s == t;
     assert this.Keys == (this as MapSubset<bv18, int>).Keys;
     assert this.Keys == (this as map<int, real>).Keys;
     assert this is map<int, real>;
    }
  }
}
