newtype{:uint32iveType "uint"} uint32 = i:int | 0 <= i < 0x100000000

method Basic() {
  var s:seq<uint32> := [1, 2, 3, 4];
  print "Head second:", s[1], "\n";
  var end := s[1..];
  print "Trunc first:", end[0], "\n";
  if end == s {
    print "Head trunc: This is unexpected\n";
    assert false;
  } else {
    print "Head trunc: This is expected\n";
  }

  var start := s[..1];
  var combine := start + end;
  if (combine == s) {
    print "Combine: This is expected\n";
  } else {
    assert false;
    print "Combine: This is unexpected\n";
  }

  var s' := s[0 := 330];
  if s[0] == 330 {
    assert false;
    print "Replace: This is unexpected\n";
  } else if s[0] != 1 {
    assert false;
    print "Replace: This is unexpected\n";
  } else {
    print "Replace: This is expected\n";
  }

  var a := new uint32[3][12, 13, 14];
  var a_seq := a[..];
  a[0] := 42;
  var a_seq' := a[..];

  if a_seq == a_seq' {
    print "Immutability: This is unexpected\n";
    assert false;
  } else {
    print "Immutability: This is expected\n";
  }
}

method ValueEquality() {
    var m0 := [1, 2, 3];
    var m1 := m0[1..];
    var m2 := [2, 3];
    if m1 == m2 {
        print "ValueEquality: This is expected\n";
    } else {
        print "ValueEquality: This is unexpected\n";
        assert false;
    }
}

method Contains() {
    var m1 := [1];
    var m2 := [1, 2];
    var m3 := [1, 2, 3];
    var m3identical := [1, 2, 3];
    var mm := [m1, m3, m1];

    if m1 in mm {
        print "Membership 1: This is expected\n";
    } else {
        print "Membership 1: This is unexpected\n";
        assert false;
    }
    if m2 in mm {
        print "Membership 2: This is unexpected\n";
        assert false;
    } else {
        print "Membership 2: This is expected\n";
    }
    if m3 in mm {
        print "Membership 3: This is expected\n";
    } else {
        print "Membership 3: This is unexpected\n";
        assert false;
    }
    if m3identical in mm {
        print "Membership 3 value equality: This is expected\n";
    } else {
        print "Membership 3 value equality: This is unexpected\n";
        assert false;
    }
}


/*
///////////////////////////////////////////////////////////////
//
//    Testing sequences from arrays
//
///////////////////////////////////////////////////////////////

method H(a: array<uint32>, c: array<uint32>, n: uint32, j: uint32)
  requires j as int < n as int == a.Length == c.Length
{
  var A := a[..];
  var C := c[..];

  if {
    case A[j] == C[j] =>
      assert a[j] == c[j];
    case forall i :: 0 <= i < n ==> A[i] == C[i] =>
      assert a[j] == c[j];
    case forall i :: 0 <= i < n ==> A[i] == C[i] =>
      assert forall i :: 0 <= i < n ==> a[i] == c[i];
    case A == C =>
      assert forall i :: 0 <= i < n ==> A[i] == C[i];
    case A == C =>
      assert forall i :: 0 <= i < n ==> a[i] == c[i];
    case true =>
  }
}

method K(a: array<uint32>, c: array<uint32>, n: uint32)
  requires n as int <= a.Length && n as int <= c.Length
{
  var A := a[..n];
  var C := c[..n];
  if {
    case A == C =>
      assert forall i :: 0 <= i < n ==> A[i] == C[i];
    case A == C =>
      assert forall i :: 0 <= i < n ==> a[i] == c[i];
    case true =>
  }
}

method L(a: array<uint32>, c: array<uint32>, n: uint32, alen:uint32)
  requires n as int <= a.Length == c.Length
  requires alen as int == a.Length
{
  var A := a[n..];
  var C := c[n..];
  var h := alen - n;
  if {
    case A == C =>
      assert forall i :: 0 <= i < h ==> A[i] == C[i];
    case A == C =>
      assert forall i :: n <= i < n + h ==> a[i] == c[i];
    case true =>
  }
}

method M(a: array<uint32>, c: array<uint32>, alen:uint32, clen:uint32, m: uint32, n: uint32, k: uint32, l: uint32)
  requires alen as int == a.Length
  requires clen as int == c.Length
  requires k as int + m as int <= a.Length
  requires l as int + n as int <= c.Length
  requires alen as int <  0x80000000
  requires clen as int < (0x100000000 / 2)
  requires k as int < (0x100000000 / 2)
  requires l as int < (0x100000000 / 2)
  requires m as int < (0x100000000 / 2)
  requires n as int < (0x100000000 / 2)
{
  if {
    case true =>
      var A := a[k..k+m];
      var C := c[l..l+n];
      if A == C {
        if * {
          assert m == n;
        } else if * {
          assert forall i :: 0 <= i < n ==> A[i] == C[i];
        } else if * {
          assert forall i {:nowarn} :: k <= i < k+n ==> A[i-k] == C[i-k];
        } else if * {
          assert forall i :: 0 <= i < n ==> A[i] == a[k+i];
        } else if * {
          assert forall i :: 0 <= i < n ==> C[i] == c[l+i];
        } else if * {
          assert forall i {:nowarn} :: 0 <= i < n ==> a[k+i] == c[l+i];
        }
      }
    case l+m <= clen && forall i :: 0 <= i < m ==> a[i] == c[l+i] =>
      assert a[..m] == c[l..l+m];
    case l+alen <= clen && forall i :: k <= i < alen ==> a[i] == c[l+i] =>
      assert a[k..] == c[l+k..l+alen];
    case l+k+m <= clen && forall i :: k <= i < k+m ==> a[i] == c[l+i] =>
      assert a[k..k+m] == c[l+k..l+k+m];
  }
}

///////////////////////////////////////////////////////////////
//
//    Testing sequence slicing
//
///////////////////////////////////////////////////////////////

method test(x:seq<uint32>)
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

function method middle<G>(s: seq<G>): G
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

method Print(s: seq<char>, i: uint32, j: uint32)
  requires i < 64 && j < 65 && s != ""
  requires |s| < 0x100000000
{
  // regression tests--these had once produced malformed Boogie in various ways
  print Base64Alphabet[i];
  print Base64Alphabet[j];  // error: index out of bounds
  if i <= j <= |s| as uint32 {
    var ch := s[i];
    var t := s[..i] + s[i..j] + s[j..];
  }
}
const Base64Alphabet := "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
*/

method Main() {
    Basic();
    ValueEquality();
    Contains();
}
