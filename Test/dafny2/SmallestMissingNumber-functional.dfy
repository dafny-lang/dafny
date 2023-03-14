// RUN: %dafny /compile:3 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Smallest missing number problem, functional version without duplicates.
// A purely functional solution to the programming problem in Richard Bird's
// "Pearls of Functional Algorithm Design".

// Rustan Leino, 22 Feb 2018

method Main() {
  var xs := Nil;
  var s := SmallestMissingNumber(xs);
  assert s == 0;
  print s, " ";  // 0
  var a := Cons(2, Cons(0, Nil));
  print SmallestMissingNumber(a), " ";  // 1
  a := Cons(3, Cons(1, a));
  print SmallestMissingNumber(a), " ";  // 4
  a := Cons(7, Cons(4, Cons(6, a)));
  print SmallestMissingNumber(a), "\n";  // 5
}

// standard definitions

datatype List<X> = Nil | Cons(head: X, tail: List<X>)

function Length(xs: List): nat
{
  match xs
  case Nil => 0
  case Cons(_, tail) => 1 + Length(tail)
}

function SmallestMissingNumber(xs: List<nat>): nat
{
  SMN(xs, 0, Length(xs))
}

function SMN(xs: List<nat>, n: nat, len: nat): nat
  requires len == Length(xs)
  decreases len
{
  if 2 <= len then
    var (L, R) := Split(xs, n + len/2);
    var llen := Length(L);
    if llen < len/2 then
      SMN(L, n, llen)
    else
      SMN(R, n + llen, len - llen)
  else if xs.Cons? then
    if xs.head == n then n + 1 else n
  else
    n
}

// Here is an alternative version, with a different splitting
// condition (using the ceiling of len/2.0 instead of the floor)
// and only two cases.
function SMN'(xs: List<nat>, n: nat, len: nat): nat
  requires len == Length(xs)
  decreases len
{
  if xs == Nil then
    n
  else
    var half := (len + 1) / 2;
    var (L, R) := Split(xs, n + half);
    var llen := Length(L);
    if llen < half then
      SMN'(L, n, llen)
    else
      SMN'(R, n + llen, len - llen)
}

// Here is yet one more version. This time, the splitting condition
// is 1 more than then floor of len/2.0. This is the version of the
// algorithm in Richard Bird's book.
function SMN''(xs: List<nat>, n: nat, len: nat): nat
  requires len == Length(xs)
  decreases len
{
  if xs == Nil then
    n
  else
    var half := len / 2 + 1;
    var (L, R) := Split(xs, n + half);
    var llen := Length(L);
    if llen < half then
      SMN''(L, n, llen)
    else
      SMN''(R, n + llen, len - llen)
}

function Split(xs: List<nat>, b: nat): (List<nat>, List<nat>)
  ensures var r := Split(xs, b); Length(xs) == Length(r.0) + Length(r.1)
{
  match xs
  case Nil => (Nil, Nil)
  case Cons(x, tail) =>
    var (L, R) := Split(tail, b);
    if x < b then
      (Cons(x, L), R)
    else
      (L, Cons(x, R))
}

// correctness theorem

lemma SmallestMissingNumber_Correct(xs: List<nat>)
  requires NoDuplicates(xs)
  ensures var s := SmallestMissingNumber(xs);
    s !in Elements(xs) &&
    forall x :: 0 <= x < s ==> x in Elements(xs)
{
  SMN_Correct(xs, 0, Length(xs));
}

ghost function Elements(xs: List): set
{
  match xs
  case Nil => {}
  case Cons(x, tail) => {x} + Elements(tail)
}

ghost predicate NoDuplicates(xs: List)
{
  match xs
  case Nil => true
  case Cons(x, tail) =>
    x !in Elements(tail) && NoDuplicates(tail)
}

// standard theorems and their proofs

lemma Cardinality(A: set, B: set)
  requires A <= B
  ensures |A| <= |B|
{
  if A != {} {
    var x :| x in A;
    Cardinality(A - {x}, B - {x});
  }
}

lemma SetEquality(A: set, B: set)
  requires A <= B && |A| == |B|
  ensures A == B
{
  if A == {} {
  } else {
    var x :| x in A;
    SetEquality(A - {x}, B - {x});
  }
}

// proof of lemmas supporting proof of main theorem

lemma SMN_Correct(xs: List<nat>, n: nat, len: nat)
  requires NoDuplicates(xs)
  requires forall x :: x in Elements(xs) ==> n <= x
  requires len == Length(xs)
  ensures var s := SMN(xs, n, len);
    n <= s <= n + len &&
    s !in Elements(xs) &&
    forall x :: n <= x < s ==> x in Elements(xs)
  decreases len
{
  if 2 <= len {
    var (L, R) := Split(xs, n + len/2);
    Split_Correct(xs, n + len/2);
    var llen := Length(L);
    Elements_Property(L);  // this is where we need the NoDuplicates property
    var bound := IntRange(n, len/2);
    Cardinality(Elements(L), bound);
    if llen < len/2 {
      SMN_Correct(L, n, llen);
    } else {
      var s := SMN(R, n + llen, len - llen);
      SMN_Correct(R, n + llen, len - llen);
      forall x | n <= x < s
        ensures x in Elements(xs)
      {
        if x < n + llen {
          SetEquality(Elements(L), bound);
        }
      }
    }
  }
}

lemma Split_Correct(xs: List<nat>, b: nat)
  requires NoDuplicates(xs)
  ensures var r := Split(xs, b);
    Elements(r.0) == (set x | x in Elements(xs) && x < b) &&
    Elements(r.1) == (set x | x in Elements(xs) && b <= x) &&
    NoDuplicates(r.0) && NoDuplicates(r.1)
{
  match xs
  case Nil =>
  case Cons(_, tail) =>
    Split_Correct(tail, b);
}

lemma Elements_Property(xs: List)
  requires NoDuplicates(xs)
  ensures |Elements(xs)| == Length(xs)
{
}

ghost function IntRange(lo: nat, len: nat): set<nat>
  ensures |IntRange(lo, len)| == len
{
  var S := set x | lo <= x < lo + len;
  assert len != 0 ==> S == IntRange(lo, len - 1) + {lo+len-1};
  S
}

// ----- Proofs of alternative versions

lemma {:vcs_split_on_every_assert} SMN'_Correct(xs: List<nat>, n: nat, len: nat)
  requires NoDuplicates(xs)
  requires forall x :: x in Elements(xs) ==> n <= x
  requires len == Length(xs)
  ensures var s := SMN'(xs, n, len);
    n <= s <= n + len &&
    s !in Elements(xs) &&
    forall x :: n <= x < s ==> x in Elements(xs)
  decreases len
{
  if xs == Nil {
  } else {
    var half := (len + 1) / 2;
    var (L, R) := Split(xs, n + half);
    Split_Correct(xs, n + half);
    var llen := Length(L);
    Elements_Property(L);  // use the NoDuplicates property
    var bound := IntRange(n, half);
    Cardinality(Elements(L), bound);
    if llen < half {
      SMN'_Correct(L, n, llen);
    } else {
      var s := SMN'(R, n + llen, len - llen);
      SMN'_Correct(R, n + llen, len - llen);
      forall x | n <= x < s
        ensures x in Elements(xs)
      {
        if x < n + llen {
          SetEquality(Elements(L), bound);
        }
      }
    }
  }
}

lemma {:vcs_split_on_every_assert} SMN''_Correct(xs: List<nat>, n: nat, len: nat)
  requires NoDuplicates(xs)
  requires forall x :: x in Elements(xs) ==> n <= x
  requires len == Length(xs)
  ensures var s := SMN''(xs, n, len);
    n <= s <= n + len &&
    s !in Elements(xs) &&
    forall x :: n <= x < s ==> x in Elements(xs)
  decreases len
{
  if xs == Nil {
  } else {
    var half := len / 2 + 1;
    var (L, R) := Split(xs, n + half);
    Split_Correct(xs, n + half);
    var llen := Length(L);
    Elements_Property(L);  // use the NoDuplicates property
    var bound := IntRange(n, half);
    Cardinality(Elements(L), bound);
    if llen < half {
      SMN''_Correct(L, n, llen);
    } else {
      var s := SMN''(R, n + llen, len - llen);
      SMN''_Correct(R, n + llen, len - llen);
      forall x | n <= x < s
        ensures x in Elements(xs)
      {
        if x < n + llen {
          SetEquality(Elements(L), bound);
        }
      }
    }
  }
}
