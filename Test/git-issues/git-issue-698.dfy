// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:py "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

type Small = x: int | 0 <= x < 100 && x != 3

function method F(x: int): int
  requires x != 3
{
  if x == 3 then 1/0 else 100
}

method Main() {
  var b := forall n: Small :: F(n) == 100;
  assert b;
  print b, "\n";
}
