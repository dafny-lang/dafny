ghost method SkippingLemma(a : array<int>, j : int)
   requires a != null;
   requires forall i :: 0 <= i < a.Length ==> 0 <= a[i];
   requires forall i :: 0 < i < a.Length ==> a[i-1]-1 <= a[i];
   requires 0 <= j < a.Length;
   ensures forall i :: j <= i < j + a[j] && i < a.Length ==> a[i] != 0;
{
   //...
}