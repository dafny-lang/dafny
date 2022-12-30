// RUN: %baredafny verify %args --relax-definite-assignment "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method MirrorImage<T>(m: array2<T>)
  modifies m
  ensures forall i,j :: 0 <= i < m.Length0 && 0 <= j < m.Length1 ==>
            m[i,j] == old(m[i, m.Length1-1-j])
{
  var a := 0;
  while a < m.Length0
    invariant a <= m.Length0
    invariant forall i,j :: 0 <= i && i < a && 0 <= j && j < m.Length1 ==>
                m[i,j] == old(m[i, m.Length1-1-j])
    invariant forall i,j :: a <= i && i < m.Length0 && 0 <= j && j < m.Length1 ==>
                m[i,j] == old(m[i,j])
  {
    var b := 0;
    while b < m.Length1 / 2
      invariant  b <= m.Length1 / 2
      invariant forall i,j :: 0 <= i && i < a && 0 <= j && j < m.Length1 ==>
                  m[i,j] == old(m[i, m.Length1-1-j])
      invariant forall j :: 0 <= j && j < b ==>
                  m[a,j] == old(m[a, m.Length1-1-j]) &&
                  old(m[a,j]) == m[a, m.Length1-1-j]
      invariant forall j :: b <= j && j < m.Length1-b ==> m[a,j] == old(m[a,j])
      invariant forall i,j :: a+1 <= i && i < m.Length0 && 0 <= j && j < m.Length1 ==>
                  m[i,j] == old(m[i,j])
    {
      m[a, m.Length1-1-b], m[a, b] := m[a, b], m[a, m.Length1-1-b];
      b := b + 1;
    }
    a := a + 1;
  }
}

method Flip<T>(m: array2<T>)
  requires m.Length0 == m.Length1
  modifies m
  ensures forall i,j :: 0 <= i < m.Length0 && 0 <= j < m.Length1 ==> m[i,j] == old(m[j,i])
{
  var N := m.Length0;
  var a := 0;
  var b := 1;
  while a != N
    invariant a < b <= N || (a == N && b == N+1)
    invariant forall i,j :: 0 <= i <= j < N ==>
                if i < a || (i == a && j < b)
                  then m[i,j] == old(m[j,i]) && m[j,i] == old(m[i,j])
                  else m[i,j] == old(m[i,j]) && m[j,i] == old(m[j,i])
    decreases N-a, N-b
  {
    if b < N {
      m[a,b], m[b,a] := m[b,a], m[a,b];
      b := b + 1;
    } else {
      a := a + 1;  b := a + 1;
    }
  }
}

method Main()
{
  var B := new bool[2,5];
  B[0,0] := true;  B[0,1] := false;  B[0,2] := false;  B[0,3] := true;  B[0,4] := false;
  B[1,0] := true;  B[1,1] := true;   B[1,2] := true;   B[1,3] := true;  B[1,4] := false;
  print "Before:\n";
  PrintMatrix(B);
  MirrorImage(B);
  print "Mirror image:\n";
  PrintMatrix(B);

  var A := new int[3,3];
  A[0,0] := 5;  A[0,1] := 7;  A[0,2] := 9;
  A[1,0] := 6;  A[1,1] := 2;  A[1,2] := 3;
  A[2,0] := 7;  A[2,1] := 1;  A[2,2] := 0;
  print "Before:\n";
  PrintMatrix(A);
  Flip(A);
  print "Flip:\n";
  PrintMatrix(A);
}

method PrintMatrix<T>(m: array2<T>)
{
  var i := 0;
  while i < m.Length0 {
    var j := 0;
    while j < m.Length1 {
      print m[i,j];
      j := j + 1;
      if j == m.Length1 {
        print "\n";
      } else {
        print ", ";
      }
    }
    i := i + 1;
  }
}
