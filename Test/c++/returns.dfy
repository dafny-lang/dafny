// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:cpp /unicodeChar:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

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
