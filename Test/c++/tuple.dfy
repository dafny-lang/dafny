// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:cpp "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

newtype uint32 = i:int | 0 <= i < 0x100000000

method ReturnTuple() returns (x:(uint32,uint32))
{
  return (1, 2);
}

method Main() {
  var x := ReturnTuple();
  var y := x.0;
  print y;
}
