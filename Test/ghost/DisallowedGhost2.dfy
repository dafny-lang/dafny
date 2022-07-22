// RUN: %dafny_0 /compile:0 /dprint:- "%s" /env:0 > "%t"
// RUN: %diff "%s.expect" "%t"

method Test()
{
  var (ghost x) := 123; // syntax error
}
