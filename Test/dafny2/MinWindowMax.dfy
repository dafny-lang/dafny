// RUN: %baredafny run %args --relax-definite-assignment "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Minimum window-max problem.
// Rustan Leino
// 1 March 2018

// The problem is to find the minimum window-max in a given array.
// A window-max is the maximum value in a contiguous subsequence of W
// array elements.
// The program is to operate in linear time.
// The following method additionally outputs the start index of the
// window-max. If that's not needed, add the keyword "ghost" in front
// of the out-parameter "start", which causes it to be erased from the
// compiled code.

method Main() {
  var a := new [][2, 3, -5, 2, 3];
  var m, start := MinimumWindowMax(a, 1);
  print "Window size 1:  min window-max is ", m, "\n";  // -5
  m, start := MinimumWindowMax(a, 2);
  print "Window size 2:  min window-max is ", m, "\n";  // 2
  m, start := MinimumWindowMax(a, 3);
  print "Window size 3:  min window-max is ", m, "\n";  // 3
  m, start := MinimumWindowMax(a, 5);
  print "Window size 5:  min window-max is ", m, "\n";  // 3
}

method MinimumWindowMax(a: array<int>, W: int) returns (m: int, start: int)
  requires 1 <= W <= a.Length
  ensures 0 <= start <= a.Length - W
  ensures m == Max(a, start, W)
  ensures forall s :: 0 <= s <= a.Length - W ==> m <= Max(a, s, W)
{
  var b := new int[a.Length];  // "b" keeps track of a descending list of maximums
  b[0] := 0;
  var k, l := 0, 1;  // only elements b[k..l] are used (and l-k <= W, so we could get away with a cyclic buffer of size W)
  var n := 1;
  while n < W
    invariant 0 <= k < l <= n <= W
    invariant StrictlyIncreasing(b, k, l, 0, n)
    invariant RightmostMax(a, 0, b[k], n)
    invariant forall u :: k < u < l ==> RightmostMax(a, b[u-1] + 1, b[u], n)
    invariant b[l-1] == n-1
    invariant l - k <= W  // this is not needed for correct, but it shows that only W of the elements of "b" are used at any given time
  {
    while k <= l-1 && a[b[l-1]] <= a[n]
      invariant k <= l <= n
      invariant forall i :: (if k < l then b[l-1] + 1 else 0) <= i < n ==> a[i] <= a[n]
    {
      l := l - 1;
    }
    b[l], l := n, l + 1;
    n := n + 1;
  }
  m := a[b[k]];
  Maxes(a, 0, b[k], n);  // by this lemma, we have m == Max(a, 0, W)

  start := 0;
  while n < a.Length
    // And here's invariant about the data structure "b", a generalization of the
    // invariant of the loop that initialized "b" above.
    invariant 0 <= k < l <= n <= a.Length
    invariant StrictlyIncreasing(b, k, l, n - W, n)
    invariant RightmostMax(a, n - W, b[k], n)  // b[k] is the index of the max of the current window
    invariant forall u :: k < u < l ==> RightmostMax(a, b[u-1] + 1, b[u], n)
    invariant b[l-1] == n-1
    // Here's the invariant we need for the "linear search" that we're doing:
    invariant 0 <= start <= a.Length - W
    invariant m == Max(a, start, W)
    invariant forall s :: 0 <= s <= n - W ==> m <= Max(a, s, W)
    invariant l - k <= W  // this is not needed for correct, but it shows that only W of the elements of "b" are used at any given time
  {
    // Extend "b" as needed
    while k <= l-1 && a[b[l-1]] <= a[n]
      invariant k <= l <= n
      invariant forall i :: (if k < l then b[l-1] + 1 else n - W) <= i < n ==> a[i] <= a[n]
    {
      l := l - 1;
    }
    b[l], l := n, l + 1;
    // Move "k" forward if index "b[k]" is no longer in the current window
    if k < l-1 && b[k] == n - W {
      k := k + 1;
    }
    // If the current window has a smaller max than what we've seen before, record it
    Maxes(a, n - W + 1, b[k], n + 1);  // by this lemma, we have a[b[k]] == Max(a, n - W + 1, W)
    if a[b[k]] < m {
      m, start := a[b[k]], n - W + 1;
    }
    n := n + 1;
    Bound(b, k, l, n, W);  // this reestablishes "l - k <= W"
  }
}

// Function Max returns the maximum value in a[s..s+len]
function Max(a: array<int>, s: int, len: int): int
  requires 0 <= s && 1 <= len && s + len <= a.Length
  reads a
{
  if len == 1 then a[s] else
    var m := Max(a, s, len - 1);
    var y := a[s + len - 1];
    if y < m then m else y
}

// Function Max's definition looks a bit cluttered, so let's prove
// a lemma that makes it clear that Max does return the maximum.
lemma MaxProperty(a: array<int>, s: int, len: int)
  requires 0 <= s && 1 <= len && s + len <= a.Length
  ensures forall i :: s <= i < s + len ==> a[i] <= Max(a, s, len)
  ensures exists i :: s <= i < s + len && a[i] == Max(a, s, len)
{
  if len == 1 {
    assert a[s] == Max(a, s, len);
  } else {
    MaxProperty(a, s, len - 1);
  }
}

// The following predicate says that a[x] is the maximum in a[lo..hi].
// More precisely, if a[lo..hi] contains several copies of the value
// a[x], then the rightmost of these values is a index "x".
predicate RightmostMax(a: array<int>, lo: int, x: int, hi: int)
  requires 0 <= lo <= x < hi <= a.Length
  reads a
{
  (forall i :: lo <= i < x ==> a[i] <= a[x]) &&
  (forall i :: x < i < hi ==> a[i] < a[x])
}

// The following lemma states a connection between RightmostMax and Max.
lemma Maxes(a: array<int>, lo: int, x: int, hi: int)
  requires 0 <= lo <= x < hi <= a.Length
  requires RightmostMax(a, lo, x, hi)
  ensures a[x] == Max(a, lo, hi - lo)
{
  MaxProperty(a, lo, hi - lo);
}

// StrictlyIncreasing states that the numbers in b[k..l] are in strictly
// increasing order and each one lies in the range lo..hi.
predicate StrictlyIncreasing(b: array<int>, k: int, l: int, lo: int, hi: int)
  requires 0 <= k <= l <= b.Length
  reads b
{
  (forall i :: k <= i < l ==> lo <= b[i] < hi) &&  // the b's are all indices into "a"
  (forall i,j :: k <= i < j < l ==> b[i] < b[j])  // the b's are in strict increasing order
}

lemma Bound(b: array<int>, k: int, l: int, n: int, W: nat)
  requires 0 <= k <= l <= b.Length
  requires forall i :: k <= i < l ==> n - W <= b[i] < n  // the b's are indices into the current window of "a"
  requires forall i,j :: k <= i < j < l ==> b[i] < b[j]  // the b's are in strict increasing order
  ensures l - k <= W
  decreases W
{
  if k < l {
    assert n - W <= b[k] < n;
    Bound(b, k+1, l, n, W-1);
  }
}
