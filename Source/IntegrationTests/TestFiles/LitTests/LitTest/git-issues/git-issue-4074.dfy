// RUN: %exits-with 4 %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method {:only "wrongArgument"} TestReported() {
  assert false; // An error here
}

method TestNotReported() {
  assert false;
}

class A {
  method {:only} TestReported() {
    assert false; // An error here
  }
  
  method TestNotReported() {
    assert false;
  }
}

module B {
  method {:only} TestReported() {
    assert false; // An error here
  }
  
  method TestNotReported() {
    assert false;
  }
}