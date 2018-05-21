method Find(a: array<int>, key: int) returns (index: int)
   requires a != null;
   ensures 0 <= index ==> index < a.Length && a[index] == key;
   ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != key;
{
   // There are many ways to fill this in. Can you write one?
}