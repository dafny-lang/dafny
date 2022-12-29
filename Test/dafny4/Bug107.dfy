// RUN: %baredafny run %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Main()
{
  var f := Inc;
	print(f(4));
}

function method Inc(x: int): int
{
  x + 2
}



