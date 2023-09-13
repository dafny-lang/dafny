// RUN: %exits-with 2 %dafny /compile:0 /dprint:- "%s" > "%t"


method Test()
{
  var (ghost x) := 123; // syntax error
}
