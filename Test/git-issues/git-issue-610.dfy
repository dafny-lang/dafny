// RUN: %testDafnyForEachCompiler "%s" -- --relax-definite-assignment

type pos = i:int | i > 0 witness 1

method Main()
{
  var x:pos;
  assert x > 0;
  var p:(pos, pos);
  var (a, b) := p;
  assert a > 0;
  assert b > 0;
  print a, " ", b, "\n";
  expect a > 0;
  expect b > 0;
}

