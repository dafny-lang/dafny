// RUN: %exits-with 4 %dafny /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

newtype int32 = int
newtype posReal = real
newtype int8 = int32

method M()
{
  var k8 := new int8[100];
  var s: set<int32>;
  var x: posReal;
  var y: posReal;
  var yOrig := y;
  var z: int32;
  x := 5.3;
  z := 12;
  s := {};
  s := {40,20};
  x := x + y;
  var r0 := x as real;
  var r1: real := 2.0 * r0;
  var i0 := z as int;
  var i1: nat := 2 * i0;
  assert i1 == 24;
  assert y == 0.0 ==> r1 == 10.6;

  assert x as real == r0;
  assert 2.0 * x as real == (2.0 * x) as real;

  assert z as int as real == i0 as real;
  assert 2 * z as int == (2 * z) as int;

  var di: int32 := z / 2 + 24 / z;
  assert di == 8;
  y := 60.0;
  var dr: posReal := y / 2.0 + 120.0 / y;
  assert dr == 32.0;

  if yOrig == 0.3 {
    var floored := r0.Floor + x.Floor;
    assert floored == 5 + 5;
    var rounded := (r0 + 0.5).Floor;
    assert rounded == 6;
  }
}

module Constraints {
  newtype SmallInt = x: int | 0 <= x < 100
  newtype LargeInt = y: int | 0 <= y < 100

  newtype A = x: int | 0 <= x
  newtype B = x: A | x < 100
  newtype C = B  // the constraints 0 <= x < 100 still apply

  ghost predicate IsEven(x: int)  // note that this is a ghost predicate
  {
    x % 2 == 0
  }
  newtype G = x: int | IsEven(x)  // it's okay to use ghost constructs in type constraints

  newtype N = nat

  newtype AssertType = s: int |
    var k := s;
    assert k <= s;
    k < 10 || 10 <= s

  newtype Te = x: int | 0 <= x < 3 && [5, 7, 8][x] % 2 != 0

  newtype Ta = x: int | 0 <= x < 3
  newtype Tb = y: Ta | [5, 7, 8][y as int] % 2 != 0  // the indexing is okay, because of the type constraint for Ta

  newtype Odds = x: int | x % 2 == 1  // error: cannot find witness

  newtype K = x: real | 10.0 <= x ==> 200.0 / (x - 20.0) < 30.0  // error: division by zero
}

module PredicateTests {
  newtype char8 = x: int | 0 <= x < 256

  method M() {
    var u: char8 := 85;
    var v: char8 := 86;
    var ch := u + v - v + u;
    assert ch + u == 255;
    ch := ch + v - 3;  // error: value out of range (for the plus operation)
  }

  method N() {
    var y: char8;
    if * {
      y := y / 2;
      y := y + 1;
      y := 300;  // error: value out of range
    } else {
      y := y + 1;  // error: value out of range
    }
  }

  method MidPoint_Bad(lo: char8, hi: char8) returns (mid: char8)
    requires lo <= hi
  {
    mid := (lo + hi) / 2;  // error: intermediate result is out of range
  }

  method MidPoint_Good(lo: char8, hi: char8) returns (mid: char8)
    requires lo <= hi
  {
    mid := lo + (hi - lo) / 2;
  }

  method MidPoint_AlsoFine(lo: char8, hi: char8) returns (mid: char8)
    requires lo <= hi
  {
    mid := ((lo as int + hi as int) / 2) as char8;
  }
}

module Module0 {
  import Module1
  method M(x: int) returns (n: Module1.N9) {
    n := x as Module1.N9;
  }
}

module Module1 {
  newtype N9 = int
}

module DatatypeCtorResolution {
  datatype Pair = Pair(int, int)

  method M() {
    var p := Pair(5, 6);
    var q: Pair;
    q := p;
    q := Pair.Pair(10, 20);
  }
}

module X {
  newtype Int = x | 0 <= x < 100
  newtype Real = r | 0.0 <= r <= 100.0

  method M() returns (i: Int, r: Real)
  {
    i := 4;
    r := 4.0;
  }

  method N()
  {
    var x := var i := 3; i;
    var y := var j := 3.0; j;
  }
}

module IntegerBasedValues {
  // Dafny allows any integer-based type, not just 'int', in the following
  // places:
  //   * array indices (any dimension)
  //   * array lengths (with new, any dimension)
  //   * sequence indicies
  //   * subsequence bounds (like sq[lo..hi])
  //   * the new multiplicity in multiset update (m[t := multiplicity])
  //   * subarray-to-sequence bounds (like a[lo..hi])
  // Note that for an array 'a', 'a.Length' is always an integer, so a
  // comparison 'i < a.Length' still requires 'i' to be an integer, not
  // any integer-based value.  Same for '|sq|' for a sequence 'sq'.

  type T

  newtype Even = x | x % 2 == 0

  method BadSpec(o: Even)
    requires 1 < o  // error: 1 is not of type Even

  method Arrays(n: nat, o: Even, i: Even, j: Even, k: nat, t: T) returns (x: T)
    requires 0 <= o && 0 <= i && 0 <= j
  {
    var a := new T[n](_ => t);
    var b := new T[o](_ => t);
    var m := new T[o, n]((_,_) => t);
    if {
      case i as int < n        =>  x := a[i];
      case i as int < a.Length =>  x := a[i];
      case i < o               =>  x := b[i];
      case i as int < b.Length =>  x := b[i];
      case k < m.Length0 && j as int < m.Length1 =>  x := m[k, j];
      case i as int < m.Length0 && k < m.Length1 =>  x := m[i, k];
      case i as int < m.Length0 && j as int < m.Length1 =>  x := m[i, j];
      case i as int < m.Length0 && j as int < m.Length1 =>  x := m[j, j];  // error: bad index 0
      case i as int < m.Length0 && j as int < m.Length1 =>  x := m[i, i];  // error: bad index 1
      case true => x := t;
    }
  }

  method Sequences(a: seq<T>, n: nat, i: Even, lo: Even, hi: Even, t: T) returns (x: T, b: seq<T>)
    requires 0 <= i && 0 <= lo <= hi
  {
    x := t;
    if {
      case i as int < |a|                   =>  x := a[i];
      case |a| % 2 == 0 && i < |a| as Even  =>  x := a[i];
      case hi as int <= |a|                 =>  b := a[lo..hi];
      case hi as int <= |a|                 =>  b := a[..hi];
      case hi as int <= |a|                 =>  b := a[0..hi];
      case lo as int <= |a|                 =>  b := a[lo..];
      case lo as int <= |a|                 =>  b := a[lo..|a|];
      case lo as int <= |a| && |a| % 2 == 0 =>  assert a[lo..|a|] == a[lo..|a| as Even];
      case n <= hi as int <= |a|            =>  b := a[n..hi];
      case lo as int <= n <= |a|            =>  b := a[lo..n];
      case (hi + hi) as int <= |a|          =>  b := a[lo..(2*hi) as Even];
      case true =>
    }
  }

  method MultisetUpdate<U>(m: multiset<U>, t: U, n: Even) returns (m': multiset<U>)
  {
    if {
      case true   =>
        m' := m[t := n];  // error: n may be negative
        m' := m[t := n+n];  // fine, if the previous statement was
      case 0 <= n =>  m' := m[t := n];
      case 0 <= n =>  m' := m[t := n+n+1];  // error: n+n+1 is not Even (like n+n and 1 are)
      case 0 <= n =>  m' := m[t := (n+n) as int + 1];
    }
  }
}

module Guessing_Termination_Metrics {
  newtype N = x | x == 0 || x == 3 || x == 7

  method M_Bad() {
    var x: N, y: N;
    while x < y
      decreases y - x  // error: y-x may not be an N
    {
      if 3 < y {
        y := 3;
      } else {
        x := 3;
      }
    }
  }

  method M_Good() {
    var x: N, y: N;
    while x < y
      decreases y as int - x as int
    {
      if 3 < y {
        y := 3;
      } else {
        x := 3;
      }
    }
  }

  method M_Inferred() {
    var x: N, y: N;
    while x < y  // the inferred decreases clause includes the type conversion to int
    {
      if 3 < y {
        y := 3;
      } else {
        x := 3;
      }
    }
  }

  newtype R = r | r == 0.0 || 10.0 <= r <= 20.0

  method P_Bad() {
    var x: R, y: R;
    while x < y
      decreases y - x  // error: y-x may not be an R
    {
      if 12.0 < y {
        y := 10.0;
      } else {
        x := 14.2;
      }
    }
  }

  method P_Good() {
    var x: R, y: R;
    while x < y
      decreases y as real - x as real
    {
      if 12.0 < y {
        y := 10.0;
      } else {
        x := 14.2;
      }
    }
  }

  method P_Inferred() {
    var x: R, y: R;
    while x < y  // the inferred decreases clause includes the type conversion to real
    {
      if 12.0 < y {
        y := 10.0;
      } else {
        x := 14.2;
      }
    }
  }
}

// ----------- test $Is predicates ----------------------------

module SeqTests {
  newtype byte = i:int | 0 <= i < 0x100

  method M0(many_bytes: seq<byte>, one_byte: byte)
    requires |many_bytes| == 1
  {
    assert 0 <= one_byte as int < 0x100;
    assert 0 <= many_bytes[0] as int < 0x100;
  }

  method M1(many_bytes: seq<byte>, many_ints: seq<int>)
    requires |many_bytes| == 1
    requires |many_ints| == 1
  {
    assert many_bytes[0] in many_bytes;
    assert many_ints[0] in many_ints;
  }

  lemma Lemma2<T>(elt: T, s: seq<T>, index: nat)
    requires index < |s|
    requires elt == s[index]
    ensures elt in s
  {}

  method M2(many_bytes: seq<byte>, many_ints: seq<int>)
    requires |many_bytes| == 1
    requires |many_ints| == 1
  {
    Lemma2(many_bytes[0], many_bytes, 0);
    Lemma2(many_ints[0], many_ints, 0);
    assert many_bytes[0] in many_bytes;
    assert many_ints[0] in many_ints;
  }

  lemma Lemma3_ints(data: seq<int>)
    requires |data| > 25
    ensures  data[0..25] == [data[0]] + data[1..25]
  {
  }

  lemma Lemma3_bytes(data: seq<byte>)
    requires |data| > 25
    ensures  data[0..25] == [data[0]] + data[1..25]
  {
  }
}
