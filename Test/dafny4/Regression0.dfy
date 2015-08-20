// RUN: %dafny /compile:0  "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This once crashed Dafny

method M() {
  var s := [1, "2"];
  if * {
    assert exists n :: n in s && n != 1;
  } else {
    assert "2" in s;
  }
}
