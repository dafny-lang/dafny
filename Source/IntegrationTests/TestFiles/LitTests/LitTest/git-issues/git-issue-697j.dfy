// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s"

method Main() {
  Tests.Test();

  AnotherTest.Test();

  SubsetTypeSubsetType.Test();
  SubsetTypeNewtype.Test();
  NewtypeSubsetType.Test();
  NewtypeNewtype.Test();

  MoreNativeTypes.Test();

  Regressions.Test0();
  Regressions.Test1();

  EvolvingNativeTypes.Test();
}

module Tests {
  predicate P(x: int) { x != 3 }

  type PlainInt = int // type synonym
  type PInt = x: int | P(x)
  type PNat = x: int | 0 <= x && P(x)

  newtype MyPlainInt = int
  newtype MyPInt = x: int | P(x)
  newtype MyPNat = x: int | 0 <= x && P(x)

  class Cell {
    const k: int
    constructor (k: int) { this.k := k; }
  }

  type Cell5 = c: Cell | c.k == 5 witness *

  method Test() {
    var nats;
    nats := set nx: nat | 2 <= nx < 5;
    print |nats|, "\n"; // 3

    var r0, r1, r2;
    r0 := set n0: PlainInt | 0 <= n0 < 5;
    r1 := set n1: PInt | 2 <= n1 < 5;
    r2 := set n2: PNat | n2 < 5;
    print |r0|, " ", |r1|, " ", |r2|, "\n"; // 5 2 4
    var b0, b1;
    b0 := forall k0: PInt | 2 <= k0 < 5 :: k0 != 3;
    b1 := forall k1: PNat | k1 < 5 :: k1 != 4;
    print b0, " ", b1, "\n"; // true false

    var s0, s1, s2;
    s0 := set m0: MyPlainInt | 0 <= m0 < 5;
    s1 := set m1: MyPInt | 2 <= m1 < 5;
    s2 := set m2: MyPNat | m2 < 5;
    print |s0|, " ", |s1|, " ", |s2|, "\n"; // 5 2 4
    b0 := forall l0: MyPInt | 2 <= l0 < 5 :: l0 as int != 3;
    b1 := forall l1: MyPNat | l1 < 5 :: l1 != 4;
    print b0, " ", b1, "\n"; // true false

    var c0 := new Cell(4);
    var c1 := new Cell(5);
    var cc: set<Cell?> := {null, c0, c1};
    var cc'0 := set y0: Cell? | y0 in cc;
    var cc'1 := set y1: Cell | y1 in cc;
    var cc'2 := set y2: Cell5 | y2 in cc;
    print |cc|, " ", |cc'0|, " ", |cc'1|, " ", |cc'2|, "\n"; // 3 3 2 1
  }
}

module AnotherTest {
  predicate P(s: seq<int>) { |s| <= 1 }

  type T = seq<int>
  type SST = s: T | P(s)

  method Test() {
    var a0: T := [];
    var a1: T := [25];
    var a2: T := [100, 101];
    var a3: T := [22];
    var S: set<T> := { a0, a1, a2, a3 };
    var s1 := set m: SST | m in S;
    print |s1|, "\n"; // 3
  }
}

module SubsetTypeSubsetType {
  predicate P(x: int) { x != 3 }

  type NonCompilableTest = x: int | P(x)
  type NonCompilableTestInt32 = x: int | -0x8000_0000 <= x < 0x8000_0000 && P(x)

  type Type0 = x: NonCompilableTest | true
  type Type1 = NonCompilableTest
  type Type2 = x: NonCompilableTestInt32 | true
  type Type3 = NonCompilableTestInt32

  predicate Q(x: int) { x != 5 }

  type CompilableTest = x: int | Q(x) && x < 8
  type Type4 = x: CompilableTest | true
  type Type5 = CompilableTest
  type Type6 = x: CompilableTest | 0 <= x

  method Test() {
    var r0, r1, r2, r3;
    r0 := set y: Type0 | 2 <= y < 6;
    r1 := set y: Type1 | 2 <= y < 6;
    r2 := set y: Type2 | 2 <= y < 6;
    r3 := set y: Type3 | 2 <= y < 6;
    print |r0|, " ", |r1|, " ", |r2|, " ", |r3|, "\n"; // 3 3 3 3

    var r4, r5, r6;
    r4 := set y: Type4 | 2 <= y;
    r5 := set y: Type5 | 2 <= y;
    r6 := set y: Type6 | 2 <= y;
    print |r4|, " ", |r5|, " ", |r6|, "\n"; // 5 5 5
  }
}

module SubsetTypeNewtype {
  predicate P(x: int) { x != 3 }

  type NonCompilableTest = x: int | P(x)
  type NonCompilableTestInt32 = x: int | -0x8000_0000 <= x < 0x8000_0000 && P(x)

  newtype Type0 = x: NonCompilableTest | true
  newtype Type1 = NonCompilableTest
  newtype Type2 = x: NonCompilableTestInt32 | true
  newtype Type3 = NonCompilableTestInt32

  predicate Q(x: int) { x != 5 }

  type CompilableTest = x: int | Q(x) && x < 8
  newtype Type4 = x: CompilableTest | true
  newtype Type5 = CompilableTest
  newtype Type6 = x: CompilableTest | 0 <= x

  method Test() {
    var r0, r1, r2, r3;
    r0 := set y: Type0 | 2 <= y < 6;
    r1 := set y: Type1 | 2 <= y < 6;
    r2 := set y: Type2 | 2 <= y < 6;
    r3 := set y: Type3 | 2 <= y < 6;
    print |r0|, " ", |r1|, " ", |r2|, " ", |r3|, "\n"; // 3 3 3 3

    var r4, r5, r6;
    r4 := set y: Type4 | 2 <= y;
    r5 := set y: Type5 | 2 <= y;
    r6 := set y: Type6 | 2 <= y;
    print |r4|, " ", |r5|, " ", |r6|, "\n"; // 5 5 5
  }
}

module NewtypeSubsetType {
  predicate P(x: int) { x != 3 }

  newtype NonCompilableTest = x: int | P(x)
  newtype NonCompilableTestInt32 = x: int | -0x8000_0000 <= x < 0x8000_0000 && P(x)

  type Type0 = x: NonCompilableTest | true
  type Type1 = NonCompilableTest
  type Type2 = x: NonCompilableTestInt32 | true
  type Type3 = NonCompilableTestInt32

  predicate Q(x: int) { x != 5 }

  newtype CompilableTest = x: int | Q(x) && x < 8
  type Type4 = x: CompilableTest | true
  type Type5 = CompilableTest
  type Type6 = x: CompilableTest | 0 <= x

  method Test() {
    var r0, r1, r2, r3;
    r0 := set y: Type0 | 2 <= y < 6;
    r1 := set y: Type1 | 2 <= y < 6;
    r2 := set y: Type2 | 2 <= y < 6;
    r3 := set y: Type3 | 2 <= y < 6;
    print |r0|, " ", |r1|, " ", |r2|, " ", |r3|, "\n"; // 3 3 3 3

    var r4, r5, r6;
    r4 := set y: Type4 | 2 <= y;
    r5 := set y: Type5 | 2 <= y;
    r6 := set y: Type6 | 2 <= y;
    print |r4|, " ", |r5|, " ", |r6|, "\n"; // 5 5 5
  }
}

module NewtypeNewtype {
  predicate P(x: int) { x != 3 }

  newtype NonCompilableTest = x: int | P(x)
  newtype NonCompilableTestInt32 = x: int | -0x8000_0000 <= x < 0x8000_0000 && P(x)

  newtype Type0 = x: NonCompilableTest | true
  newtype Type1 = NonCompilableTest
  newtype Type2 = x: NonCompilableTestInt32 | true
  newtype Type3 = NonCompilableTestInt32

  predicate Q(x: int) { x != 5 }

  newtype CompilableTest = x: int | Q(x) && x < 8
  newtype Type4 = x: CompilableTest | true
  newtype Type5 = CompilableTest
  newtype Type6 = x: CompilableTest | 0 <= x

  method Test() {
    var r0, r1, r2, r3;
    r0 := set y: Type0 | 2 <= y < 6;
    r1 := set y: Type1 | 2 <= y < 6;
    r2 := set y: Type2 | 2 <= y < 6;
    r3 := set y: Type3 | 2 <= y < 6;
    print |r0|, " ", |r1|, " ", |r2|, " ", |r3|, "\n"; // 3 3 3 3

    var r4, r5, r6;
    r4 := set y: Type4 | 2 <= y;
    r5 := set y: Type5 | 2 <= y;
    r6 := set y: Type6 | 2 <= y;
    print |r4|, " ", |r5|, " ", |r6|, "\n"; // 5 5 5
  }
}

module MoreNativeTypes {
  type LoSubset = x: int | -0x8000_0000 <= x
  newtype LoNewtype = x: int | -0x8000_0000 <= x

  newtype Int32a = x: LoSubset | x < 0x8000_0000
  newtype Int32b = x: LoNewtype | x < 0x8000_0000

  type Int32c = x: Int32a | x != 3
  type Int32d = x: Int32b | x != 3
  newtype Int32e = x: Int32a | x != 3
  newtype Int32f = x: Int32b | x != 3

  method Test() {
    var r0, r1;
    r0 := set y: Int32a | 2 <= y < 6;
    r1 := set y: Int32b | 2 <= y < 6;

    var r2, r3, r4, r5;
    r2 := set y: Int32c | 2 <= y < 6;
    r3 := set y: Int32d | 2 <= y < 6;
    r4 := set y: Int32e | 2 <= y < 6;
    r5 := set y: Int32f | 2 <= y < 6;

    print |r0|, " ", |r1|, " ", |r2|, " ", |r3|, " ", |r4|, " ", |r5|, "\n"; // 4 4 3 3 3 3
  }
}

module Regressions {
  type byte = x | x < 256 && x != 7 && 0 <= x

  predicate P(x: int) { x == 7 || x == 9 }

  method Test0() {
    var s := set b: byte | 5 <= b < 12 && P(b as int);
    assert 9 in s;
    var u :| u in s;
    print u, "\n"; // 9
  }

  // -----------------------------

  newtype NewByte = x | x < 256 && x != 7 && 0 <= x

  newtype ByteBase = x: int | x != 7
  type Byyyte = x: ByteBase | x < 256 && 0 <= x

  predicate Filter(x: int) {
    x % 2 == 1 && x < 10
  }

  method Test1() {
    var s := set b: byte | Filter(b as int);
    var t := set b: NewByte | Filter(b as int);
    var u := set b: Byyyte | Filter(b as int);

    print |s|, " ", |t|, " ", |u|, "\n"; // 4 4 4
  }
}

module EvolvingNativeTypes {
  newtype Nat = x: int | 0 <= x && x != 1
  newtype uint32 = x: Nat | x < 0x1_0000_0000 && x != 3
  newtype byte = x: uint32 | x < 256 && x != 5
  newtype Not7Either = x: byte | x != 7

  predicate R(x: int) {
    match x
    case 5 => true
    case 1 | 3 | 7 | 9 => true
    case _ => false
  }

  method Test() {
    assert R(7);
    var u: byte :| R(u as int) && u != 9;
    assert R(9);
    var v: Not7Either :| R(v as int);
    print u, " ", v, "\n"; // 7 9
  }
}
