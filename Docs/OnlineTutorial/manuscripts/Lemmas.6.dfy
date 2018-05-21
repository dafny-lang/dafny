ghost method SkippingLemma(a : array<int>, j : int)
   requires a != null;
   requires forall i :: 0 <= i < a.Length ==> 0 <= a[i];
   requires forall i :: 0 < i < a.Length ==> a[i-1]-1 <= a[i];
   requires 0 <= j < a.Length;
   ensures forall k :: j <= k < j + a[j] && k < a.Length ==> a[k] != 0; 
{
   var i := j;
   while(i < j + a[j] && i < a.Length)
      invariant i < a.Length ==> a[j] - (i-j) <= a[i];
      invariant forall k :: j <= k < i && k < a.Length ==> a[k] != 0; 
   {
      i := i + 1;
   }
}

method FindZero(a: array<int>) returns (index: int)
   requires a != null;
   requires forall i :: 0 <= i < a.Length ==> 0 <= a[i];
   requires forall i :: 0 < i < a.Length ==> a[i-1]-1 <= a[i];
   ensures index < 0  ==> (forall i :: 0 <= i < a.Length ==> a[i] != 0);
   ensures 0 <= index ==> (index < a.Length && a[index] == 0);
{
   index := 0;
   while (index < a.Length)
      invariant 0 <= index;
      invariant forall k :: 0 <= k < index && k < a.Length ==> a[k] != 0;
   {
      if (a[index] == 0) { return; }
      SkippingLemma(a, index);
      index := index + a[index];
   }
   index := -1;
}