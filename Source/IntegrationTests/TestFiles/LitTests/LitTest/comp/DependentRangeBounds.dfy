// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s"

// A bound on a bound variable may depend on a variable that is enumerated later. That variable's bounds are then
// substituted for it: an upper bound where the dependent bound grows with the variable, a lower bound where it
// shrinks, and each of them where there are several.

newtype u8 = x: int | 0 <= x < 0x100
newtype u64 = x: int | 0 <= x < 0x1_0000_0000_0000_0000
newtype i32 = x: int | -0x8000_0000 <= x < 0x8000_0000
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

  // A product of nonnegative factors grows with them, so k's lower bound gives one for k * k, which breaks the cycle of
  // j's and k's bounds, while low, which can be negative, gives none for j * j.
  var cycle := set i: int, j: int, k: int {:nowarn} | 0 <= k <= j < (i - 1) * (i - 1) + 1 && k * k <= i < 3 :: (i, j, k);
  var low := -5;
  var floored := set i: int, j: int {:nowarn} | 0 <= j < 3 && low <= j && j * j <= i < 10 :: (i, j);
  print |cycle|, " ", |floored|, "\n";

  // Bounds that neither grow nor shrink with a later variable, which neither this order nor its reverse can use, the
  // second time with a k that needs only one of its two bounds.
  var dips := set i: int, j: int, k: int {:nowarn} | 0 <= j < 3 && 0 <= k < (j - 1) * (j - 1) + 1 && 0 <= i < k * k :: (i, j, k);
  var optional := set i: int, j: int, k: int {:nowarn} | 0 <= j < 4 && 0 <= k < (j - 1) * (j - 1) + 1 && 0 <= i < k * k && k < i + 50 :: (i, j, k);
  print |dips|, " ", |optional|, "\n";

  // The same through bounds of other kinds: a sequence's length, membership in a set and in a sequence, and an
  // equality.
  var S := {[1, 2], [3], []};
  var lengths := set s: seq<int>, i: int, j: int {:nowarn} | s in S && 0 <= j < |s| && 0 <= i < s[j] :: (s, i, j);
  var SS := {{1, 2}, {3}};
  var inSets := set x: int, i: int, s: set<int> {:nowarn} | s in SS && x in s && 0 <= i < x :: (i, x);
  var Q := {[1, 3]};
  var inSeqs := set x: int, i: int, q: seq<int> {:nowarn} | q in Q && x in q && 0 <= i < x :: (i, x);
  var equal := set k: int, i: int, j: int {:nowarn} | 0 <= j < 3 && k == 2 * j + 1 && 0 <= i < k :: (i, j, k);
  print |lengths|, " ", |inSets|, " ", |inSeqs|, " ", |equal|, "\n";
  var MS := {multiset{2}};
  var inMultisets := set x: int, i: int, m: multiset<int> {:nowarn} | m in MS && x in m && 0 <= i < x :: (i, x);
  var M := {map[1 := 0, 4 := 0]};
  var inMaps := set x: int, i: int, m: map<int, int> {:nowarn} | m in M && x in m && 0 <= i < x :: (i, x);
  var TT := {{1, 2}};
  var subsets := set s: set<int>, i: int, t: set<int> {:nowarn} | t in TT && s <= t && 0 <= i < |s| :: (s, i);
  print |inMultisets|, " ", |inMaps|, " ", |subsets|, "\n";

  // The compiler gets copies of quantifiers that the trigger generator splits, which have to enumerate j first too,
  // and of binding guards and quantifiers whose matching loop it rewrites with a variable for j - 1 or j + k, which
  // then appears in i's bound and so has to come after j and k but before i, however they are declared. The term that
  // such a variable stands for can have a quantifier in it.
  var splitForall := set x: int {:nowarn} | 0 <= x < 2 && forall i: int, j: int | 0 <= j < 3 && 0 <= i < (j - 1) * (j - 1) + 1 :: Small(i) && Low(j);
  var splitExists := set x: int {:nowarn} | 0 <= x < 2 && exists i: int, j: int | 0 <= j < 3 && 0 <= i < (j - 1) * (j - 1) + 1 :: Small(i) || Low(j);
  if i: int, j: int :| 0 <= j < 5 && 0 <= i < (j - 1) * (j - 1) + 1 && i * j == 2 {
    print |splitForall|, " ", |splitExists|, " ", i, " ", j, "\n";
  }
  var rewritten := set x: int {:nowarn} | 0 <= x < 2 && exists j: int, k: int, i: int | 0 <= j < 3 && 0 <= k < 3 && 0 <= i < (j + k) * (j + k) + 1 :: i * j == 2 && i * k == 2;
  var quantified := forall i | 0 <= i < 3 :: Id(i) <= Id(i + (if exists x {:nowarn} | 0 <= x < 2 :: x == 1 then 1 else 0));
  if j: int, i: int :| 0 <= j < 5 && 0 <= i < (j - 1) * (j - 1) + 1 && i * j == 2 {
    print |rewritten|, " ", quantified, " ", i, " ", j, "\n";
  }

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
  // 10 - (j - 2) * (j - 2) first grows and then shrinks as j grows, so no bound of j can replace it, and this
  // enumerates j first.
  forall i, j | 0 <= j < 5 && 0 <= i < 10 - (j - 2) * (j - 2) {
    a[i, j] := a[i, j] + 1;
  }
  var count := 0;
  for i := 0 to 10 {
    for j := 0 to 5 {
      count := count + a[i, j];
    }
  }
  var x: int, y: int :| 0 <= y < 1 && 0 <= x < 10 - y && x * x == 81;
  print count, " ", x, " ", y, " ", Root(), "\n";

  // 9 - j at j's bound 10 is -1, which u8 and u64 do not hold, and j's bound e + 1 is 256.
  var lowered := set i: u8, j: u8 {:nowarn} | j <= 9 && 9 - j <= i < 20 :: (i, j);
  var lowered64 := set i: u64, j: u64 {:nowarn} | j <= 9 && 9 - j <= i < 20 :: (i, j);
  var e: u8 := 255;
  var squared := set i: int, j: u8 {:nowarn} | j <= e && 0 <= i < (j as int) * (j as int) && i < 300 && i + 1 == (j as int) * (j as int) :: j;
  print |lowered|, " ", |lowered64|, " ", |squared|, "\n";

  // Native variables that only another order bounds by more than their type's limits, up to which they would be
  // enumerated otherwise: the reverse order, a cascade, and a b and c that bound each other.
  var modulo := set i: u64, j: u64 {:nowarn} | j < 10 && i < j % 3 + 1 :: (i, j);
  var moduloCascade := set i: u64, j: u64, k: u64 {:nowarn} | j < 3 && k < j % 3 + 1 && i < k * k :: (i, j, k);
  var signed := set c: i32, b: i32, a: i32 {:nowarn} | 0 <= b < 3 && 3 - b <= c < b * b + 1 && c <= a < c * c :: (a, b, c);
  print |modulo|, " ", |moduloCascade|, " ", |signed|, "\n";

  // Either of j's two upper bounds can be the tighter one.
  var huge: u64, ten: u64 := 0x100_0000_0000, 10;
  var belowTen := set i: u64, j: u64 {:nowarn} | j < 10 && j < huge && i < j :: (i, j);
  var belowVariable := set i: u64, j: u64 {:nowarn} | j < 0x100_0000_0000 && j < ten && i < j :: (i, j);
  var s := [10, 20, 30, 40, 50];
  var indexPairs := set i: uint32, j: uint32 {:nowarn} | j < |s| && i < j :: (i, j);
  print |belowTen|, " ", |belowVariable|, " ", |indexPairs|, "\n";
}

predicate Small(i: int) { i < 5 }
predicate Low(j: int) { j < 3 }
function Id(x: int): int { x }

function Root(): int {
  var i: int, j: int :| 0 <= j < 1 && 0 <= i < 10 - j && i * i == 81; i
}
