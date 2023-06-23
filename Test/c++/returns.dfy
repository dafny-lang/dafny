// RUN: %testDafnyForEachCompiler "%s" -- --relax-definite-assignment --spill-translation --unicode-char:false

newtype uint64 = i:int | 0 <= i < 0x10000000000000000

method multi() returns (x:uint64, y:uint64)
{
  x := 1;
  y := 2;
}

method Main()
{
  var x, y := multi();
  print x, y, '\n';
}
