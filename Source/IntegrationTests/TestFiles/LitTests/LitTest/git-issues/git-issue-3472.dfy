// RUN: %baredafny build --no-verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype X = Set(s: set<int>)

method Foo(xs: X) {
  match xs {
    case Set(s: set<int>) => 
      var x :| x in s;
  }
}