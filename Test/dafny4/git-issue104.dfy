// RUN: %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

predicate method bug(a: array<int>)
    reads a
{
    forall i, j | 0 <= i <= j < a.Length :: a[i] <= a[j]
}
