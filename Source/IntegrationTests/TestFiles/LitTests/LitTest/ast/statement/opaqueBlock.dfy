// RUN: ! %verify %s --bprint /Users/rwillems/SourceCode/dafny/opaque.bpl &> "%t"
// RUN: %diff "%s.expect" "%t"

method Foo() returns (x: int)
  ensures x > 4 
{
  x := 1;
  var y := 1;
  opaque
    ensures x > 3 
  {
    x := x + y;
    x := x + 2;
  }
  assert x == 4; // error
  x := x + 1;
}