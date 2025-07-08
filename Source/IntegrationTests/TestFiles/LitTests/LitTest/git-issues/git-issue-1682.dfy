// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"


method IsUnique(str: array<char>) returns (ret: bool)
{
  ret := multiset
}
