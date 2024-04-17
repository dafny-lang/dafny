// RUN: %exits-with 2 %verify --type-system-refresh --general-newtypes "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Fields {
  newtype Bool = bool {
    var x: int // error: a newtype is not allowed to have a mutable field
  }
}

module Members {
  method Test() {
    var b: Bool := true;
    b.PrintMe(); // true 15 4
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

    method PrintMe() { // error: not allowed to redeclare a member called PrintMe
    }

    function F(x: int): int { // error: not allowed to redeclare a member called F
      x + 2
    }

    twostate lemma n() { // error: not allowed to redeclare a member called n
    }
  }

  newtype BoolBoolBool = b: BoolBool | b witness true {
    function H(x: int): int { // error: not allowed to declare a member called H
      2
    }
  }

  newtype Int = int {
    static method P<X>(x: X) {
      print "Int.P: ", x, "\n";
    }
  }
  
  newtype Real = real {
    const Floor: int := 10 // error: not allowed to redeclare a member called Floor
    method M() {
      var a := Floor;
      var b := this.Floor;
      var c := (this as real).Floor;
    }
  }
  newtype TooReal = r: real | 2.7 <= r < 3.14 witness 3.000 {
    method M() {
      var a := Floor;
      var b := this.Floor;
      var c := (this as real).Floor;
    }
  }
  
  newtype Bv = x: bv7 | x != 31 {
    method RotateLeft(u: int) // error: not allowed to redeclare a member called RotateLeft
    method M() {
      var a := RotateRight(2);
      var b := this.RotateRight(2);
      var c := (this as bv7).RotateRight(2);
    }
  }
  
  newtype Map = map<int, real> {
    const k: set<int> := Keys
    method M() returns (s: set<int>) {
      s := k;
    }

    predicate Values(r: real) // error: not allowed to redeclare a member named Values
    predicate Items(r: real) // error: not allowed to redeclare a member named Items
  }
  
  newtype IMap = m: imap<int, real> | 10.0 !in m.Values {
    predicate Keys(r: real) // error: not allowed to redeclare a member named Keys
    predicate Values(r: real) // error: not allowed to redeclare a member named Values

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
    }
  }
}

module MemberIsNotInBaseType {
  newtype IntSet = set<int> {
    static predicate P(x: int) { x != 118 }
    method M(u: int) {
      var s := set x | 0 <= x < 200 && P(x);
      if u in this {
        assert u in s + this;
      }
      var t := s as set<int>;
      assert P(0);
      assert s.P(0);
      assert t.P(0); // error: set<int> does not have a member P
    }
  }
}
