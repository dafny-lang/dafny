// RUN: %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

predicate method bug(a: array<int>)
    requires a != null
    reads a
{
    forall i, j | 0 <= i <= j < a.Length :: a[i] <= a[j]
}
