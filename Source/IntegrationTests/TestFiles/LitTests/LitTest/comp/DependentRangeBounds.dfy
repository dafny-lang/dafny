// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s"

// A bound on a bound variable may depend on a variable that is enumerated later. That variable's bounds are then
// substituted for it: an upper bound where the dependent bound grows with the variable, a lower bound where it
// shrinks, and each of them where there are several.

newtype u8 = x: int | 0 <= x < 0x100
newtype u64 = x: int | 0 <= x < 0x1_0000_0000_0000_0000
type uint32 = x: int | 0 <= x < 0x1_0000_0000

method Main() {
  // Bounds that shrink as j grows, with the conjuncts in either order.
  var pairs := set i: int, j: int {:nowarn} | 0 <= i < 10 - j && 0 <= j < 5 :: (i, j);
  var swapped := set i: int, j: int {:nowarn} | 0 <= j < 5 && 0 <= i < 10 - j :: (i, j);
  assert (9, 0) in swapped;
  print |pairs|, " ", |swapped|, " ", (9, 0) in swapped, "\n";

  var sums := set i: int, j: int {:nowarn} | 0 <= i && 0 <= j < 5 && i + j < 10 :: (i, j);
  var negated := set i: int, j: int {:nowarn} | 0 <= j < 5 && -j <= i < 3 :: (i, j);
  print |sums|, " ", |negated|, "\n";

  // A cascade of substitutions, and a bound that a multiplication makes shrink.
  var cascade := set i: int, j: int, k: int {:nowarn} | 0 <= k < 3 && k <= j < 5 && 0 <= i < 10 - j :: (i, j, k);
  var scaled := set i: int, j: int, k: int {:nowarn} | 0 <= j < 5 && 0 <= i < 10 - 2 * j && 0 <= k < i :: (i, j, k);
  print |cascade|, " ", |scaled|, "\n";

  // Bounds under multiplications and divisions by constants, parentheses, and conversions.
  var doubled := set i: int, j: int, k: int {:nowarn} | 0 <= j < 5 && 0 <= i < 2 * j && 0 <= k < i :: (i, j, k);
  var halved := set i: int, j: int, k: int {:nowarn} | 0 <= j < 10 && 0 <= i < j / 2 && 0 <= k < i :: (i, j, k);
  var grouped := set i: int, j: int, k: int {:nowarn} | 0 <= j < 5 && 0 <= i < (j) + 1 && 0 <= k < i :: (i, j, k);
  var converted := set i: int, j: u8, k: int {:nowarn} | j < 5 && 0 <= i < j as int && 0 <= k < i :: (i, j, k);
  print |doubled|, " ", |halved|, " ", |grouped|, " ", |converted|, "\n";

  print forall i: int, j: int {:nowarn} | 0 <= j < 5 && 0 <= i < 10 - j :: i + j < 9, "\n";

  var a := new int[10, 5];
  forall i, j | 0 <= j < 5 && 0 <= i < 10 - j {
    a[i, j] := 1;
  }
  var count := 0;
  for i := 0 to 10 {
    for j := 0 to 5 {
      count := count + a[i, j];
    }
  }
  var x: int, y: int :| 0 <= y < 1 && 0 <= x < 10 - y && x * x == 81;
  print count, " ", x, " ", y, " ", Root(), "\n";

  // 9 - j at j's bound 10 is -1, which u8 and u64 do not hold.
  var lowered := set i: u8, j: u8 {:nowarn} | j <= 9 && 9 - j <= i < 20 :: (i, j);
  var lowered64 := set i: u64, j: u64 {:nowarn} | j <= 9 && 9 - j <= i < 20 :: (i, j);
  print |lowered|, " ", |lowered64|, "\n";

  // Either of j's two upper bounds can be the tighter one.
  var huge: u64, ten: u64 := 0x100_0000_0000, 10;
  var belowTen := set i: u64, j: u64 {:nowarn} | j < 10 && j < huge && i < j :: (i, j);
  var belowVariable := set i: u64, j: u64 {:nowarn} | j < 0x100_0000_0000 && j < ten && i < j :: (i, j);
  var s := [10, 20, 30, 40, 50];
  var indexPairs := set i: uint32, j: uint32 {:nowarn} | j < |s| && i < j :: (i, j);
  print |belowTen|, " ", |belowVariable|, " ", |indexPairs|, "\n";
}

function Root(): int {
  var i: int, j: int :| 0 <= j < 1 && 0 <= i < 10 - j && i * i == 81; i
}
