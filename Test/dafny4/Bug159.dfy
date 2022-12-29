// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method ArrayInit(n: nat) returns (a: array<int>)
  ensures a.Length == n
  ensures forall i :: 0 <= i < n ==> a[i] == i
{
  a := new int[n];
  forall i | 0 <= i < n {
    a[i] := i;
  }
}

method Init(m: array2<int>)
  modifies m
  ensures forall i,j :: 0 <= i < m.Length0 && 0 <= j < m.Length1 ==> m[i,j] == 0
{
  forall i,j | 0 <= i < m.Length0 && 0 <= j < m.Length1 {
    m[i,j] := 0;
  }
}

method Gradient(n: nat) returns (m: array2<int>)
  ensures m.Length0 == m.Length1 == n
  ensures forall i,j :: 0 <= i < n && 0 <= j < n ==> m[i,j] == j+i
{
  m := new int[n,n];
  forall i,j | 0 <= i < n && 0 <= j < n {
    m[i,j] := i+j;
  }
}

method M3(C: array3<real>)
  modifies C
  ensures forall i,j,k ::
    0 <= i < C.Length0 && 0 <= j < C.Length1 && 0 <= k < C.Length2
    ==> C[i,j,k] == 0.0
{
  forall i,j,k | 0 <= i < C.Length0 && 0 <= j < C.Length1 && 0 <= k < C.Length2
  {
    C[i,j,k] := 0.0;
  }
}
