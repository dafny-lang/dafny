// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s"

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

method Main() {
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

  // TODO: check a compilable constraint with a non-compilable base type
}
