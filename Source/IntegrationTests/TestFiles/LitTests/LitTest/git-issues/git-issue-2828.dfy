// RUN: %exits-with 2 %build "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method M()
{
  assert arr[0];
}
