// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method main() {
  var arr: array<int>;
  assert(multiset(arr[..]) == multiset(arr[..arr.Length]));
}