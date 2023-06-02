// RUN: %dafny /compile:3 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Main()
{
  var f := Inc;
	print(f(4));
}

function Inc(x: int): int
{
  x + 2
}



