predicate sorted(a: array<int>)
   requires a != null;
   reads a;
{
   forall j, k :: 0 <= j < k < a.Length ==> a[j] <= a[k]
}

method BinarySearch(a: array<int>, value: int) returns (index: int)
   requires a != null && 0 <= a.Length && sorted(a);
   ensures 0 <= index ==> index < a.Length && a[index] == value;
   ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != value;
{
   // This one is a little harder. What should go here?
}