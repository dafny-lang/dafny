// RUN: %dafny  /compile:3 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method lol() returns (c: int)
{
  c := 5;
  return c;
}
