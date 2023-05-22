// RUN: %dafny /compile:3 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Rustan Leino
// 12 April 2015
// VerifyThis 2015
// Problem 1 -- Relaxed Prefix

// The property IsRelaxedPrefix is defined in terms of an auxiliary function.  The
// auxiliary function allows a given number (here, 1) of elements to be dropped from
// the pattern.
ghost predicate IsRelaxedPrefix<T>(pat: seq<T>, a: seq<T>)
{
  IsRelaxedPrefixAux(pat, a, 1)
}

// This predicate returns whether or not "pat", dropping up to "slack" elements, is
// a prefix of "a".
ghost predicate IsRelaxedPrefixAux<T>(pat: seq<T>, a: seq<T>, slack: nat)
{
  // if "pat" is the empty sequence, the property holds trivially, regardless of the slack
  if pat == [] then true
  // if both "pat" and "a" are nonempty and they agree on their first element, then the property
  // holds iff it holds of their drop-1 suffixes
  else if a != [] && pat[0] == a[0] then IsRelaxedPrefixAux(pat[1..], a[1..], slack)
  // if either "a" is empty or "pat" and "a" disagree on their first element, then the property
  // holds iff there's any slack left and the property holds after spending 1 slack unit and dropping
  // the first element of the pattern
  else slack > 0 && IsRelaxedPrefixAux(pat[1..], a, slack-1)
}

// Here is the corrected reference implementation.  The specification says to return true iff
// "pat" is a relaxed prefix of "a".
method ComputeIsRelaxedPrefix<T(==)>(pat: seq<T>, a: seq<T>) returns (b: bool)
  ensures b == IsRelaxedPrefix(pat, a)
{
  // This implementation is the given reference implementation but with two corrections.  One
  // correction is the out-of-bounds error in the indexing of "a".  This is corrected here by
  // strengthening the guard of the while loop.  The other correction is that after the loop, the
  // property still holds if "a" has been exhausted but the number of elements left to inspect in
  // the pattern does not exceed the number of elements we are still allowed to drop.  (There are
  // other ways the given reference implementation could have been fixed as well.)
  ghost var B := IsRelaxedPrefixAux(pat, a, 1);  // the answer we want
  var shift, i := 0, 0;
  while i < |pat| && i-shift < |a|
    invariant 0 <= i <= |pat| && i-shift <= |a|
    invariant 0 <= shift <= i
    invariant shift == 0 || shift == 1
    invariant IsRelaxedPrefixAux(pat[i..], a[i-shift..], 1-shift) == B
  {
    if pat[i] != a[i-shift] {
      if shift == 0 {
        shift := 1;
      } else {
        return false;
      }
    }
    i := i + 1;
  }
  return i - shift <= |pat| <= i - shift + 1;
}

method Main()
{
  var a := [1,3,2,3];
  var b := ComputeIsRelaxedPrefix([1,3], a);
  print b, "\n";
  b := ComputeIsRelaxedPrefix([1,2,3], a);
  print b, "\n";
  b := ComputeIsRelaxedPrefix([1,2,4], a);
  print b, "\n";
}

// Here is an alternative definition of IsRelaxedPrefix.  Perhaps this definition more obviously
// follows the English description of "relaxed prefix" given in the problem statement.
ghost predicate IRP_Alt<T>(pat: seq<T>, a: seq<T>)
{
  // "pat" is a relaxed prefix of "a"
  // if "pat" is an actual prefix of "a"
  pat <= a ||
  // or if after dropping one element from "pat", namely the one at an index "k", then the result
  // is a prefix of "a"
  exists k :: 0 <= k < |pat| && pat[..k] + pat[k+1..] <= a
}

// We prove that the alternate definition is the same as the one given above.
lemma AreTheSame_Theorem<T>(pat: seq<T>, a: seq<T>)
  ensures IsRelaxedPrefix(pat, a) == IRP_Alt(pat, a)
{
  // Prove <==
  if IRP_Alt(pat, a) {
    if pat <= a {
      Same0(pat, a);
    } else if exists k :: 0 <= k < |pat| && pat[..k] + pat[k+1..] <= a {
      var k :| 0 <= k < |pat| && pat[..k] + pat[k+1..] <= a;
      Same1(pat, a, k);
    }
    assert IsRelaxedPrefix(pat, a);
  }
  // Prove ==>
  if IsRelaxedPrefix(pat, a) {
    Same2(pat, a);
    assert IRP_Alt(pat, a);
  }
}
lemma Same0<T>(pat: seq<T>, a: seq<T>)
  requires pat <= a
  ensures IsRelaxedPrefixAux(pat, a, 1)
{
}
lemma Same1<T>(pat: seq<T>, a: seq<T>, k: nat)
  requires 0 <= k < |pat| && pat[..k] + pat[k+1..] <= a
  ensures IsRelaxedPrefixAux(pat, a, 1)
{
  // "k" gives one splitting point, but we want to last splitting point
  var d := k;
  while d+1 < |pat| && pat[d] == pat[d+1]
    invariant 0 <= d < |pat| && pat[..d] + pat[d+1..] <= a
  {
    d := d + 1;
  }
  Same1_Aux(pat, a, d);
}
lemma Same1_Aux<T>(pat: seq<T>, a: seq<T>, k: nat)
  requires 0 <= k < |pat| && pat[..k] + pat[k+1..] <= a && (k+1 == |pat| || pat[k] != pat[k+1])
  ensures IsRelaxedPrefixAux(pat, a, 1)
{
  if k+1 == |pat| {
    assert pat[..k] + pat[k+1..] == pat[..k] <= a;
    if k == 0 {
    } else {
      assert IsRelaxedPrefixAux(pat, a, 1) == IsRelaxedPrefixAux(pat[1..], a[1..], 1);
      Same1_Aux(pat[1..], a[1..], k-1);
    }
  } else if k == 0 {
    assert pat[..0] + pat[1..] == pat[1..];
    assert pat[1] == a[0];
    assert pat[0] != pat[1];
    assert IsRelaxedPrefixAux(pat, a, 1) == IsRelaxedPrefixAux(pat[1..], a, 0);
    Prefix(pat[1..], a);
  } else {
    calc ==> {
      true;
      pat[..k] + pat[k+1..] <= a;
      (pat[..k] + pat[k+1..])[1..] <= a[1..];
      pat[..k][1..] + pat[k+1..] <= a[1..];
      { assert pat[..k][1..] == pat[1..][..k-1]; }
      pat[1..][..k-1] + pat[k+1..] <= a[1..];
      { assert pat[k+1..] == pat[1..][k..]; }
      pat[1..][..k-1] + pat[1..][k..] <= a[1..];
    }
    Same1_Aux(pat[1..], a[1..], k-1);
  }
}
lemma Prefix<T>(pat: seq<T>, a: seq<T>)
  requires pat <= a
  ensures IsRelaxedPrefixAux(pat, a, 0)
{
}
lemma Same2<T>(pat: seq<T>, a: seq<T>)
  requires IsRelaxedPrefixAux(pat, a, 1)
  ensures IRP_Alt(pat, a)
{
  if pat == [] {
  } else if a != [] && pat[0] == a[0] {
    if pat[1..] <= a[1..] {
    } else {
      var x := a[0];
      var k :| 0 <= k < |pat[1..]| && pat[1..][..k] + pat[1..][k+1..] <= a[1..];
      calc {
        pat[1..][..k] + pat[1..][k+1..] <= a[1..];
      ==  { assert pat[1..][k+1..] == pat[k+2..]; }
        pat[1..][..k] + pat[k+2..] <= a[1..];
      ==
        [x] + (pat[1..][..k] + pat[k+2..]) <= [x] + a[1..];
      ==  { assert [x] + a[1..] == a; }
        [x] + (pat[1..][..k] + pat[k+2..]) <= a;
      ==  { assert [x] + (pat[1..][..k] + pat[k+2..]) == pat[..k+1] + pat[k+2..]; }
        pat[..k+1] + pat[k+2..] <= a;
      }
    }
  } else {
    Same2_Prefix(pat[1..], a);
    assert pat[1..] <= a;
    assert 0 <= 0 < |pat| && pat[..0] + pat[0+1..] <= a;
  }
}
lemma Same2_Prefix<T>(pat: seq<T>, a: seq<T>)
  requires IsRelaxedPrefixAux(pat, a, 0)
  ensures pat <= a
{
}
