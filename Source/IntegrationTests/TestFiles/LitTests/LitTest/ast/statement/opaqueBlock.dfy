// RUN: ! %verify %s --bprint /Users/rwillems/SourceCode/dafny3/opaque.bpl &> "%t"
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

class Wrapper {
 var x: int
}

method ContainingMethodModifies(wrapper: Wrapper, unchangedWrapper: Wrapper) returns (x: int)
  modifies wrapper
  ensures x > 4 
{
  wrapper.x := 2;
  opaque
    ensures wrapper.x > 3 
  {
    wrapper.x := wrapper.x + 2;
    unchangedWrapper.x := 10; // error
  }
  x := wrapper.x + 1;
}

method ExplicitModifies(wrapper: Wrapper) returns (x: int)
  modifies wrapper
  ensures x > 4 
{
  wrapper.x := 2;
  opaque
    ensures wrapper.x > 3 
    modifies {}
  {
    wrapper.x := wrapper.x + 2; // error
  }
  x := wrapper.x + 1;
}

method ModifiesTooMuch(wrapper: Wrapper, unchangedWrapper: Wrapper)
  modifies wrapper
{
  opaque
    modifies wrapper, unchangedWrapper // error
  {
    unchangedWrapper.x := 10;
  }
}

method Nested(w1: Wrapper, w2: Wrapper)
  modifies w1, w2
{
  opaque
    modifies w1 
  {
    opaque modifies w2 // error 
    {
      w2.x := 10;
    }
  }
}

method DefiniteAssignment()
{
  var x: int; 
  opaque
    ensures x == 3
  {
    x := 3;
  } 
  var target := x;
  var y: int;
  opaque
  {
    y := 4;
  }
  target := y;
}