predicate sorted(a: array<int>)
   reads a;
{
   // Change this definition to treat null arrays as "not sorted".
   // (i.e. return false for null arrays)
   forall j, k :: 0 <= j < k < a.Length ==> a[j] <= a[k]
}