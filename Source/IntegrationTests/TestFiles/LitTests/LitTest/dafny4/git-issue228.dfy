// RUN: %exits-with 4 %dafny /env:0 /dprint:- "%s" > "%t"
// RUN: %exits-with 4 %dafny /env:0 /rprint:- "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

// Tests the pretty printing of + and *

lemma Sequences(s: seq, t: seq, u: seq)
  // It's okay to drop the first set of parens here, but not the second:
  ensures (s + t) + u == s + (t + u)
{
}

lemma Sets(s: set, t: set, u: set)
  // In each of the following lines,
  // it's okay to drop the first set of parens here, but not the second:
  ensures (s + t) + u == s + (t + u)
  ensures (s * t) * u == s * (t * u)
{
}

method Numerics() returns (x: int, n: nat, r: real, o: ORDINAL, b: bv0, c: bv19)
{
  // All of the following can be printed without any parentheses:
  x := (x + x) + (x + x);
  n := (n + n) + (n + n);
  r := (r + r) + (r + r);
  o := (o + o) + (o + o);
  b := (b + b) + (b + b);
  c := (c + c) + (c + c);
}

newtype NegIsOdd = x | x < 0 ==> x % 2 == 1 witness 1
newtype Byte = x | 0 <= x < 256

method ConstrainedIntermediateExpressions(a: NegIsOdd, b: NegIsOdd, x: Byte, z: Byte)
  requires 0 <= b && z == 0
{
  // The following two lines demonstrate that `+` really isn't always associative
  // for a `newtype`. So pretty printing had better keep the parentheses in
  // the first line.
  var c0 := a + (b + b);  // fine (non-negative can be doubled, and adding an even is always fine)
  var c1 := (a + b) + b;  // error: intermediate expression may not be a `NegIsOdd`

  // The following two lines demonstrate that `*` really isn't always associative
  // for a `newtype`. So pretty printing had better keep the parentheses in
  // the first line.
  var d0 := x * (x * z);  // fine
  var d1 := (x * x) * z;  // error: intermediate expression may not be a `Byte`
}

type Subset_NegIsOdd = x | x < 0 ==> x % 2 == 1 witness 1
type Subset_Byte = x | 0 <= x < 256

method SubsetTypes(a: Subset_NegIsOdd, b: Subset_NegIsOdd, x: Subset_Byte, z: Subset_Byte)
  requires 0 <= b && z == 0
{
  // Intermediate expressions of subset types don't have to satify the subtype
  // constraint, so all of the lines below are okay, and they can also be printed
  // completely without parentheses.

  var c0 := a + (b + b);
  var c1 := (a + b) + b;

  var d0 := x * (x * z);
  var d1 := (x * x) * z;
}
