// RUN: %resolve "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function {:opaque} mul(a: int, b: int): int
{
  a * b
}

method M()
{
  reveal mul;
}
