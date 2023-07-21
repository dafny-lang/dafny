// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method test(arr: array<int>) {
  assert(multiset(arr[..]) == multiset(arr[..arr.Length]));
}