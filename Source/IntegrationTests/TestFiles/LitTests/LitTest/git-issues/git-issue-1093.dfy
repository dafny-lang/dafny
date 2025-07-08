// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s" -- --relax-definite-assignment

method Main() {
  UnusedLabel();
  var c := new C;
  c.x := 4;
  c.LabelUsedInGhostCode();  // 10
  print c.x, "\n";
}

method UnusedLabel()
{
  // The following once resulted in malformed Go code, in particular generating an unused labeled.
  label foo: {}
}

class C {
  var x: int

  method LabelUsedInGhostCode()
    modifies this
  {
    x := x + 2;
    label A:
    x := x + 1;
    label B:
    x := x + 3;
    assert x == old(x) + 6;
    assert x == old@A(x) + 4;
    assert old@B(x) + x == 2 * old(x) + 9;
  }
}
