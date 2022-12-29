// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Test various ways to get to the members of a datatype

datatype DT = Make | Create(w: int) {
  static const b := 30
  const c := 40
  function method F(): int {
    if Make? then 92 else 95
  }
}

method Test0() {
  var d: DT := Make;
  var x := d.c;
  var y := d.b;
  var f := d.F;
  assert x == 40 && y == 30 && f() == 92;
}

method Test1() {
  var d: DT := Create(2);
  var x := d.c;
  var y := d.b;
  var f := d.F;
  assert x == 40 && y == 30 && f() == 95;
}

method Test2() {
  // The following three mentions of "Make." once complained about "Make" being an unresolved identifier
  var x := Make.c;
  var y := Make.b;
  var f := Make.F;
  assert x == 40 && y == 30 && f() == 92;
}

method Test3() {
  var x := Make().c;
  var y := Make().b;
  var f := Make().F;
  assert x == 40 && y == 30 && f() == 92;
}

method Tesst4() {
  var x := Create(2).c;
  var y := Create(2).b;
  var f := Create(2).F;
  assert x == 40 && y == 30 && f() == 95;
}

method Test4() {
  var x := DT.Make.c;
  var y := DT.Make.b;
  var f := DT.Make.F;
  assert x == 40 && y == 30 && f() == 92;
}
