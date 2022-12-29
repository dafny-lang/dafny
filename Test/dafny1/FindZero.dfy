// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method FindZero(a: array<int>) returns (r: int)
  requires forall i :: 0 <= i < a.Length ==> 0 <= a[i];
  requires forall i :: 0 <= i && i+1 < a.Length ==> a[i]-1 <= a[i+1];
  ensures 0 <= r ==> r < a.Length && a[r] == 0;
  ensures r < 0 ==> forall i :: 0 <= i < a.Length ==> a[i] != 0;
{
  var n := 0;
  while (n < a.Length)
    invariant forall i :: 0 <= i < n && i < a.Length ==> a[i] != 0;
  {
    if (a[n] == 0) { r := n; return; }
    Lemma(a, n, a[n]);
    n := n + a[n];
  }
  r := -1;
}

lemma Lemma(a: array<int>, k: int, m: int)
  requires forall i :: 0 <= i < a.Length ==> 0 <= a[i];
  requires forall i :: 0 <= i && i+1 < a.Length ==> a[i]-1 <= a[i+1];
  requires 0 <= k;
  requires k < a.Length ==> m <= a[k];
  ensures forall i :: k <= i < k+m && i < a.Length ==> a[i] != 0;
  decreases m;
{
  if (0 < m && k < a.Length) {
    assert a[k] != 0;
    Lemma(a, k+1, m-1);
  }
}

// -----------------------------------------------------------------

method FindZero_GhostLoop(a: array<int>) returns (r: int)
  requires forall i :: 0 <= i < a.Length ==> 0 <= a[i];
  requires forall i :: 0 <= i && i+1 < a.Length ==> a[i]-1 <= a[i+1];
  ensures 0 <= r ==> r < a.Length && a[r] == 0;
  ensures r < 0 ==> forall i :: 0 <= i < a.Length ==> a[i] != 0;
{
  var n := 0;
  while (n < a.Length)
    invariant forall i :: 0 <= i < n && i < a.Length ==> a[i] != 0;
  {
    if (a[n] == 0) { return n; }
    ghost var m := n;
    while (m < n + a[n])
      invariant m <= n + a[n] && m < a.Length;
      invariant n + a[n] - m <= a[m];
      invariant forall i :: 0 <= i < m && i < a.Length ==> a[i] != 0;
    {
      m := m + 1;
      if (m == a.Length) { break; }
    }
    n := n + a[n];
  }
  return -1;
}

// -----------------------------------------------------------------

method FindZero_Assert(a: array<int>) returns (r: int)
  requires forall i :: 0 <= i < a.Length ==> 0 <= a[i];
  requires forall i {:nowarn} {:matchinglooprewrite false}:: 0 <= i-1 && i < a.Length ==> a[i-1]-1 <= a[i];
  ensures 0 <= r ==> r < a.Length && a[r] == 0;
  ensures r < 0 ==> forall i :: 0 <= i < a.Length ==> a[i] != 0;
{
  var n := 0;
  while (n < a.Length)
    invariant forall i :: 0 <= i < n && i < a.Length ==> a[i] != 0;
  {
    if (a[n] == 0) { return n; }
    assert forall m {:induction} :: n <= m < n + a[n] && m < a.Length ==> n+a[n]-m <= a[m];
    n := n + a[n];
  }
  return -1;
}
