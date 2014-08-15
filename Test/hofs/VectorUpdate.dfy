// RUN: %dafny /compile:3 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method VectorUpdate(N: int, a : array<A>, f : (int,A) -> A)
  requires a != null;
  requires N == a.Length;
  requires forall j :: 0 <= j < N ==> f.requires(j,a[j]);
  requires forall j :: 0 <= j < N ==> a !in f.reads(j,a[j]);
  modifies a;
  ensures forall j :: 0 <= j < N ==> a[j] == f(j,old(a[j]));
{
  var i := 0;
  while (i < N)
    invariant 0 <= i <= N;
    invariant forall j :: i <= j < N ==> f.requires(j,a[j]);
    invariant forall j :: 0 <= j < N ==> f.requires(j,old(a[j]));
    invariant forall j :: i <= j < N ==> a !in f.reads(j,a[j]);
    invariant forall j :: i <= j < N ==> a[j] == old(a[j]);
    invariant forall j :: 0 <= j < i ==> a[j] == f(j,old(a[j]));
  {
    a[i] := f(i,a[i]);
    i := i + 1;
  }
}

method Main() 
{
  var v := new int[10];
  // Hey, works as an initialiser:
  VectorUpdate(10, v, (i,_) => i);
  PrintArray(v);
  VectorUpdate(10, v, (_,x) => x + 1);
  PrintArray(v);
  // Phew, now they are all positive, so we can do:
  VectorUpdate(10, v, (_,x) requires x != 0 => 100 / x);
  PrintArray(v);
  var u := new int[10];
  // Hey, works as a copy as well!
  VectorUpdate(10, u, (i,_) requires 0 <= i < 10 reads v => v[i]);
  PrintArray(u);
  // Having some fun with the index:
  var z := new int[9];
  VectorUpdate(9, z, (i,_) requires 0 <= i < 9 reads u => u[i] + u[i+1]);
  PrintArray(z);
  assert z[8] == 21; // voila, the prover also knows what's going on
}

method PrintArray(a : array<int>)
  requires a != null;
{
  var i := 0;
  while (i < a.Length) {
    if (i != 0) {
	  print ", ";
	}
    print a[i];
    i := i + 1;
  }
  print "\n";
}
