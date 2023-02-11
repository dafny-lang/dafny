// RUN: %exits-with 2 %baredafny resolve --use-basename-for-filename "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function {:opaque} mul(a: int, b: int): int
{
  a * b
}

method M()
{
  reveal mul;
}
