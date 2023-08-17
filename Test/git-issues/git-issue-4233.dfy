// RUN: %testDafnyForEachCompiler "%s"

newtype MyReal = real

method Main() {
  var x: MyReal := 12.0 / 10.0;
  print x, "\n"; // expect 1.2

  if x == 1.0 {
    assert false;
    print "unreachable\n";
  }
}
