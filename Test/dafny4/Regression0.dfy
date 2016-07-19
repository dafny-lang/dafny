// RUN: %dafny /compile:0  "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This once crashed Dafny

method M() {
  var s := [1, "2"];  // error: all elements must have the same type
  if * {
    assert exists n :: n in s && n != 1;  // the type of n is inferred to be int
  } else {
    assert "2" in s;  // error: since the type of s wasn't determined
  }
}
