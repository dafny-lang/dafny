// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s"

// A range's bounds are computed before the conjuncts they rely on are checked: in a set comprehension, the conjuncts
// that mention the bounded variable or one enumerated after it, and in a forall statement or a quantifier, all of
// them. So next to another bound, a bound is used only if computing it cannot fail, and in place of the type's own
// bound only if it lies in the range of its type.

newtype u8 = x: int | 0 <= x < 0x100
type Pos = x: u8 | 0 < x witness 1

function Hundred(x: Pos): u8 { 100 / x }

method Main() {
  // i * j == 1 makes 100 / j defined, but the range of i is computed for j = 0 as well.
  var s := set j: int, i: int {:nowarn} | 0 <= j < 3 && 0 <= i < 5 && i * j == 1 && i < 100 / j :: (i, j);
  print |s|, "\n";

  // Neither 100 / k nor n - 1, which is -1 rather than a u8, can bound i where k and n are 0.
  var a := new int[5];
  var k: u8, n: u8 := 0, 0;
  forall i: u8 | 0 < k && 0 <= i < 100 / k && (i as int) < a.Length {
    a[i] := 1;
  }
  forall i: u8 | n > 0 && n - 1 <= i < n && (i as int) < a.Length {
    a[i] := 2;
  }
  print a[0], " ", forall i: u8 {:nowarn} | n > 0 && n - 1 <= i < n :: i == 3, "\n";

  // Hundred(k) divides by k, which only the type of its parameter keeps nonzero.
  print forall i: u8 {:nowarn} | 0 < k && i < Hundred(k) :: i < 100, "\n";
}
