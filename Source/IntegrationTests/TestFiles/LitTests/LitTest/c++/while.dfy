// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s" -- --relax-definite-assignment --spill-translation --allow-deprecation --unicode-char false

newtype uint32 = i:int | 0 <= i < 0x100000000

method Main() {
  var x:uint32 := 0;

  while (x < 10) {
    print x, "\n";
    x := x + 1;
  }

  print "\n";

  x := 0;
  while (x < 10) {
    print x, "\n";
    if (x == 5) { break; }
    x := x + 1;
 }
}
