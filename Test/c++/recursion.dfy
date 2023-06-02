// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:cpp /unicodeChar:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

newtype uint32 = i:int | 0 <= i < 0x100000000

method R0(x:bool)
{
  if x {
    print "x\n";
    R1(false);
  } else {
    print "!x\n";
  }
}

method R1(y:bool)
{
  if y {
    print "y\n";
    R0(false);
  } else {
    print "!y\n";
  }
}

method CallSelf(x:uint32) {
  if x == 0 {
    print "Done\n";
  } else {
    print x, "\n";
    CallSelf(x - 1);
  }
}

method Main() {
  R0(true);
  CallSelf(3);
}
