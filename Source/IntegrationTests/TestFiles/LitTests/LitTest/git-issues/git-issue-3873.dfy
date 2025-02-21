// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s"

method Main() {
  M0();
  M1();
}

method M0() {
  var a := new ()[1];
  var m: map<array<()>, ()> := map[a := ()];
  var v :| v in m by {
    assert a in m;
  }
  print v[0], "\n";
}

method M1() {
  var a := new ()[1];
  var v :| v in map[a := ()];
  print v[0], "\n";
}
