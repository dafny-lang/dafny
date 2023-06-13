// RUN: %dafny /compile:3 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Smallest missing number.
// An imperative solution to the programming problem in Richard Bird's
// "Pearls of Functional Algorithm Design".
// Rustan Leino, 19 Feb 2018

method Main() {
  var a := new nat[][3, 6, 23, 9];
  var s := SmallestMissing(a);
  print s, "\n";  // 0
  a := new nat[][3, 2, 0, 5, 4];
  s := SmallestMissing(a);
  print s, "\n";  // 1
  a := new nat[][2, 4, 6, 0, 1, 3, 100];
  s := SmallestMissing(a);
  print s, "\n";  // 5
  a := new nat[0];  // empty array
  s := SmallestMissing(a);
  print s, "\n";  // 0
}

ghost predicate Has<T>(a: array<T>, x: T)
  reads a
{
  exists i :: 0 <= i < a.Length && a[i] == x
}

method SmallestMissing(a: array<nat>) returns (s: nat)
  ensures forall i :: 0 <= i < a.Length ==> a[i] != s  // s is missing
  ensures forall x :: 0 <= x < s ==> Has(a, x)  // all numbers smaller than s are present
{
  var N := a.Length;  // for brevity
  // Insight: Because we're only given N numbers, we know the result will be at most N.
  // Strategy: First, record which numbers in the range 0..N exist in "a". Second, pick the smallest
  // one not encountered.
  // Note: Apparently, Richard Bird's book unnecessarily uses N+1 instead of N as the length
  // of the auxiliary array.
  var e := new bool[N](_ => false);  // new array initialized with all "false"
  forall n | 0 <= n < N && a[n] < N {
    e[a[n]] := true;
  }
  s := 0;
  while s < N && e[s]
    invariant 0 <= s <= N
    invariant forall j :: 0 <= j < s ==> Has(a, j)
  {
    s := s + 1;
  }
  if s == N {
    Lemma(a);
  }
}

// If an array "a" contains every number below "a.Length", then it only contains numbers below "a.Length"
lemma Lemma(a: array<nat>)
  requires forall x :: 0 <= x < a.Length ==> Has(a, x)
  ensures forall i :: 0 <= i < a.Length ==> a[i] < a.Length
{
  var ms := multiset(a[..]);
  var i, ns := 0, multiset{};
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall x :: x in ns ==> 0 <= x < i
    invariant |ns| == i && ns <= ms
  {
    assert Has(a, i);
    ns := ns + multiset{i};
    i := i + 1;
  }
  assert |ms - ns| == 0;
  forall i | 0 <= i < a.Length
    ensures a[i] < a.Length
  {
    assert a[i] in ms;
  }
}

// Alternative implementation

// This version uses a loop to initialize "e".
method SmallestMissing_Loop(a: array<nat>) returns (s: nat)
  ensures forall i :: 0 <= i < a.Length ==> a[i] != s  // s is missing
  ensures forall x :: 0 <= x < s ==> Has(a, x)  // all numbers smaller than s are present
{
  var N := a.Length;  // for brevity
  // Insight: Because we're only given N numbers, we know the result will be at most N.
  // Strategy: First, record which numbers in the range 0..N exist in "a". Second, pick the smallest
  // one not encountered.
  var e := new bool[N](_ => false);  // new array initialized with all "false"
  var n := 0;
  while n < N
    invariant 0 <= n <= N
    // every number in the range 0..N encountered in "a" so far has been marked off in "e"
    invariant forall i :: 0 <= i < n && a[i] < N ==> e[a[i]]
    // every number that is marked off in "e" exists in "a"
    invariant forall j :: 0 <= j < N && e[j] ==> Has(a, j)
  {
    if a[n] < N {
      e[a[n]] := true;
    }
    n := n + 1;
  }
  s := 0;
  while s < N && e[s]
    invariant 0 <= s <= N
    invariant forall j :: 0 <= j < s ==> Has(a, j)
  {
    s := s + 1;
  }
  if s == N {
    Lemma(a);
  }
}
