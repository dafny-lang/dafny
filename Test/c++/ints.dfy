// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:cpp /unicodeChar:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

newtype sbyte = i:int | -0x80 <= i < 0x80
newtype byte = i:int | 0 <= i < 0x100
newtype int16 = i:int | -0x8000 <= i < 0x8000
newtype uint16 = i:int | 0 <= i < 0x10000
newtype int32 = i:int | -0x80000000 <= i < 0x80000000
newtype uint32 = i:int | 0 <= i < 0x100000000
newtype int64 = i:int | -0x8000000000000000 <= i < 0x8000000000000000
newtype uint64 = i:int | 0 <= i < 0x10000000000000000
newtype nat8 = i:int | 0 <= i < 0x80
newtype nat16 = i:int | 0 <= i < 0x8000
newtype nat32 = i:int | 0 <= i < 0x80000000
newtype nat64 = i:int | 0 <= i < 0x8000000000000000

method Division(a:int64)
  requires 0 <= a < 0x1_0000_0000
{
  var z := a / 2;
  print z;
}

method Main() {
  var x:uint32 := 40;
  var y:uint32 := 2;
  var z := x + y;

  print "Result is z = ", z, "\n";
}
