// RUN: %exits-with 2 %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This once crashed Dafny

method M() {
  var s := [1, "2"];  // error: all elements must have the same type (type of s not yet determined)
  if * {
    assert "2" in s;  // error: mismatched types  (*)
  } else if * {
    assert exists n :: n in s && n != 1;  // error: mismatched types  (*)
  }

  // (*) Depending on what type is inferred for "s", it may be that only one of the two (*)'s is reported as an error.
}
