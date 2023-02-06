// RUN: %testDafnyForEachCompiler "%s"

method Main() {
  Sequences();
  Arrays();
  print "that's all, folks!\n";
}

method Sequences() {
  var a1 := [42];
  var a2 := [42];
  assert a1 == a2;
  expect a1 == a2;
}

method Arrays() {
  var a1 := new int[] [42];
  var a2 := new int[] [42];
  assert a1 != a2;
  expect a1 != a2;
}
