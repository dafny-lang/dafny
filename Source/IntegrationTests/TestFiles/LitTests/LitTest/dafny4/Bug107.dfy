// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s" -- --relax-definite-assignment

method Main()
{
  var f := Inc;
	print(f(4));
}

function Inc(x: int): int
{
  x + 2
}



