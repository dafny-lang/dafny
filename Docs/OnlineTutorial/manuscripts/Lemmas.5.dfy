ghost method SkippingLemma(a : array<int>, j : int)
   requires a != null;
   requires forall i :: 0 <= i < a.Length ==> 0 <= a[i];
   requires forall i :: 0 < i < a.Length ==> a[i-1]-1 <= a[i];
   requires 0 <= j < a.Length - 3;
   // Note: the above has been changed so that the array indices below are good.
{
   assert a[j  ] - 1 <= a[j+1];
   assert a[j+1] - 1 <= a[j+2];
   assert a[j+2] - 1 <= a[j+3];
   // therefore:
   assert a[j  ] - 3 <= a[j+3];
}