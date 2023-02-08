// RUN: %testDafnyForEachCompiler -- /compile:4 /noVerify "%s" > "%t"

method Main() {
  var i: int := 42;
  assert {:expect} i == 41;
  print "Done\n";
}
