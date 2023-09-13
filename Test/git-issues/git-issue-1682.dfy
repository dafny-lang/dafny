// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"
// RUN: %diff "%s.expect" "%t"

method IsUnique(str: array<char>) returns (ret: bool)
{
  ret := multiset
}
