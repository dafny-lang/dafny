// RUN: %dafny_0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method M()
{
  assert arr[0];
}
