// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"


method Main() {
  Tests.Test();
  SubsetTypeSubsetType.Test();
  SubsetTypeNewtype.Test();
  NewtypeSubsetType.Test();
  NewtypeNewtype.Test();
}

module Tests {
  ghost predicate P(x: int) { x != 3 }

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
    r1 := set n1: PInt | 2 <= n1 < 5; // error: this set comprehension is not compilable
    r2 := set n2: PNat | n2 < 5; // error: this set comprehension is not compilable
    print |r0|, " ", |r1|, " ", |r2|, "\n"; // 5 2 4
    var b0, b1;
    b0 := forall k0: PInt | 2 <= k0 < 5 :: k0 != 3; // error: this set comprehension is not compilable
    b1 := forall k1: PNat | k1 < 5 :: k1 != 4; // error: this set comprehension is not compilable
    print b0, " ", b1, "\n"; // true false

    var s0, s1, s2;
    s0 := set m0: MyPlainInt | 0 <= m0 < 5;
    s1 := set m1: MyPInt | 2 <= m1 < 5; // error: this set comprehension is not compilable
    s2 := set m2: MyPNat | m2 < 5; // error: this set comprehension is not compilable
    print |s0|, " ", |s1|, " ", |s2|, "\n"; // 5 2 4
    b0 := forall l0: MyPInt | 2 <= l0 < 5 :: l0 as int != 3; // error: this set comprehension is not compilable
    b1 := forall l1: MyPNat | l1 < 5 :: l1 != 4; // error: this set comprehension is not compilable
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

// check a compilable constraint with a non-compilable base type

module SubsetTypeSubsetType {
  ghost predicate P(x: int) { x != 3 }

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
    r0 := set y: Type0 | 2 <= y < 6; // error: this set comprehension is not compilable
    r1 := set y: Type1 | 2 <= y < 6; // error: this set comprehension is not compilable
    r2 := set y: Type2 | 2 <= y < 6; // error: this set comprehension is not compilable
    r3 := set y: Type3 | 2 <= y < 6; // error: this set comprehension is not compilable
    print |r0|, " ", |r1|, " ", |r2|, " ", |r3|, "\n"; // 3 3 3 3

    var r4, r5, r6;
    r4 := set y: Type4 | 2 <= y;
    r5 := set y: Type5 | 2 <= y;
    r6 := set y: Type6 | 2 <= y;
    print |r4|, " ", |r5|, " ", |r6|, "\n"; // 5 5 5
  }
}

module SubsetTypeNewtype {
  ghost predicate P(x: int) { x != 3 }

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
    r0 := set y: Type0 | 2 <= y < 6; // error: this set comprehension is not compilable
    r1 := set y: Type1 | 2 <= y < 6; // error: this set comprehension is not compilable
    r2 := set y: Type2 | 2 <= y < 6; // error: this set comprehension is not compilable
    r3 := set y: Type3 | 2 <= y < 6; // error: this set comprehension is not compilable
    print |r0|, " ", |r1|, " ", |r2|, " ", |r3|, "\n"; // 3 3 3 3

    var r4, r5, r6;
    r4 := set y: Type4 | 2 <= y;
    r5 := set y: Type5 | 2 <= y;
    r6 := set y: Type6 | 2 <= y;
    print |r4|, " ", |r5|, " ", |r6|, "\n"; // 5 5 5
  }
}

module NewtypeSubsetType {
  ghost predicate P(x: int) { x != 3 }

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
    r0 := set y: Type0 | 2 <= y < 6; // error: this set comprehension is not compilable
    r1 := set y: Type1 | 2 <= y < 6; // error: this set comprehension is not compilable
    r2 := set y: Type2 | 2 <= y < 6; // error: this set comprehension is not compilable
    r3 := set y: Type3 | 2 <= y < 6; // error: this set comprehension is not compilable
    print |r0|, " ", |r1|, " ", |r2|, " ", |r3|, "\n"; // 3 3 3 3

    var r4, r5, r6;
    r4 := set y: Type4 | 2 <= y;
    r5 := set y: Type5 | 2 <= y;
    r6 := set y: Type6 | 2 <= y;
    print |r4|, " ", |r5|, " ", |r6|, "\n"; // 5 5 5
  }
}

module NewtypeNewtype {
  ghost predicate P(x: int) { x != 3 }

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
    r0 := set y: Type0 | 2 <= y < 6; // error: this set comprehension is not compilable
    r1 := set y: Type1 | 2 <= y < 6; // error: this set comprehension is not compilable
    r2 := set y: Type2 | 2 <= y < 6; // error: this set comprehension is not compilable
    r3 := set y: Type3 | 2 <= y < 6; // error: this set comprehension is not compilable
    print |r0|, " ", |r1|, " ", |r2|, " ", |r3|, "\n"; // 3 3 3 3

    var r4, r5, r6;
    r4 := set y: Type4 | 2 <= y;
    r5 := set y: Type5 | 2 <= y;
    r6 := set y: Type6 | 2 <= y;
    print |r4|, " ", |r5|, " ", |r6|, "\n"; // 5 5 5
  }
}
