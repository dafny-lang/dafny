// RUN: %exits-with 2 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method IsUnique(str: array<char>) returns (ret: bool)
{
  ret := multiset
}
