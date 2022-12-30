// RUN: %exits-with 2 %baredafny verify %args --print=- "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Test()
{
  var (ghost x) := 123; // syntax error
}
