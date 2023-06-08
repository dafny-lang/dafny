// RUN: %dafny /compile:3 /rprint:"%t.rprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type Small = x: int | 0 <= x < 100 && x != 3

function F(x: int): int
  requires x != 3
{
  if x == 3 then 1/0 else 100
}

method Main() {
  var b := !exists n: Small :: F(n) != 100;
  assert b;
  print b;
}