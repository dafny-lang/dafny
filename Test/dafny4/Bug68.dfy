// RUN: %dafny /compile:3  "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Main()
{
  var m := map [[10, 20] := 33];
  assert [10, 20] in m; // succeeds 
  print [10, 20] in m; // prints False
}