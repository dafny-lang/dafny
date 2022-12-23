// RUN: %exits-with 2 %dafny /compile:0  "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This once crashed Dafny

method M() {
  var s := [1, "2"];  // error: all elements must have the same type (type of s not yet determined)
  if * {
    assert "2" in s;  // This causes the type of s to be inferred as seq<string>.
  } else if * {       // Thus, the n in the next line is inferred as string (or seq<char>)
    assert exists n :: n in s && n != 1;  // error: mismatched types
  }
}
