// RUN: %exits-with 4 %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method test(x:seq<int>)
  requires |x| == 10
{
  var elts := x[4:2:3];
  var a, b, c := elts[0], elts[1], elts[2];

  assert |a| == 4;
  assert |b| == 2;
  assert |c| == 3;

  assert forall i :: 0 <= i < |a| ==> a[i] == x[i];
  assert forall i :: 0 <= i < |b| ==> b[i] == x[i+4];
  assert forall i :: 0 <= i < |c| ==> c[i] == x[i+6];

  var elts2 := x[1:5:];  // Leaving off the last length puts the remaining elements in the last seq
  var d, e, f := elts2[0], elts2[1], elts2[2];
  assert |d| == 1;
  assert |e| == 5;
  assert |f| == |x| - (|d| + |e|);

  assert forall i :: 0 <= i < |d| ==> d[i] == x[i];
  assert forall i :: 0 <= i < |e| ==> e[i] == x[i+1];
  assert forall i :: 0 <= i < |f| ==> f[i] == x[i+6];
}

newtype MyNumeric = n | 0 <= n < 100

method NumericSlice<T>(x: seq<T>, two: MyNumeric) returns (y: seq<T>)
  requires 10 <= |x| && two == 2
  ensures |y| == 3
{
  var slices;
  if * {
    slices := x[0:two:3:0:];
  } else {
    slices := x[1 : 1 : 1 : 3 : two : two : 0];
    assert |slices[5]| == 2;
  }
  assert |slices| == 5 || |slices| == 7;
  return middle(slices);
}

function middle<G>(s: seq<G>): G
  requires |s| % 2 == 1
{
  s[|s| / 2]
}

method MoreTests<T>(s: seq<T>)
  requires 10 <= |s|
{
  var t := [3.14, 2.7, 1.41, 1985.44, 100.0, 37.2][1:0:3];
  assert |t| == 3 && t[0] == [3.14] && t[1] == [] && t[2] == [2.7, 1.41, 1985.44];

  var u := [true, false, false, true][1:1:];
  assert |u| == 3 && u[0][0] && !u[1][0] && u[2] == [false, true];

  assert s[10:][0] == s[..10];
  assert s[10:][1] == s[10..];
}

method Print(s: seq<char>, i: bv24, j: bv10)
  requires i < 64 && j < 65 && s != ""
{
  // regression tests--these had once produced malformed Boogie in various ways
  print Base64Alphabet[i];
  print Base64Alphabet[j];  // error: index out of bounds
  if i as int <= j as int <= |s| {
    var ch := s[i >> 18];
    var t := s[..i] + s[i..j] + s[j..];
  }
}
const Base64Alphabet := "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";

