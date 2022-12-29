// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %baredafny run %args --no-verify --target=cs "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=js "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=go "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=java "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=py "%s" "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

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
