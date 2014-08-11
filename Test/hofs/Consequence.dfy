// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Check() {
  var f : nat -> nat;
  assume f.requires(0);
  var i : nat := f(0);
}

