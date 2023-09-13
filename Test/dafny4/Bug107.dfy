// RUN: %testDafnyForEachCompiler "%s" --refresh-exit-code=0 -- --relax-definite-assignment

method Main()
{
  var f := Inc;
	print(f(4));
}

function Inc(x: int): int
{
  x + 2
}



