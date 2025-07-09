// RUN: ! %verify --standard-libraries=true %s &> "%t"
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
  x := x + y;
}

method StructuredCommandsIf(t: bool)
{
  var x := 1;
  opaque 
  {
    if (t) {
      x := x + 2;
    } 
  }
  assert x >= 1; // error
}

method StructuredCommandsWhile()
{
  var x := 1;
  opaque 
  {
    while (x > 0)
      decreases x 
    {
      x := x - 1;
    } 
  }
  assert x >= 1; // error
}

method BadlyFormedSpec()
{
  var x := 1;
  opaque 
    ensures 3 / x == 1 // error: possible division by zero
  {
    x := 3;
  }
  var y;
  opaque ensures y == y { } // error: y is not assigned
  y := 1;
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
  target := y; // error: !assigned(y) 
  var z: int;
  opaque 
    ensures z == z // error !assigned(z)
  {
    if (*) {
      z := 5;
    }
  }
  target := z;
}

method EnsuresDoesNotHold() {
  var x: int;
  opaque 
    ensures false
  {
    x := 3;
  }
}

import opened Std.Wrappers
method Returns(input: Option<int>) returns (r: Option<int>)
  requires input.Some? ==> input == Some(3)
{
  var x: int; 
  opaque
    ensures x == 3
  {
    x :- input;
  } 
  var y: int;
  opaque
  {
    y := 4;
    return Some(y);
  }
  var z: int;
  opaque
    ensures z > 5
  {
    z :| z > 10;
  }
  r := Some(z);
}

method MultipleAssignment() returns (r: int) {
  var tuple := (3,2);
  var x: int;
  var y: int;  
  opaque
    ensures x == 3
  {
    x, y := tuple.0, tuple.1;
  }
  r := x;
}

method FlattenedMatch(x: Option<int>, y: Option<int>) {
   // This match statement must copy some of the case bodies when flattening
   var z := 3;
   opaque {
     match (x, y) {
       case (Some(a), _) =>
         var y := a;
       case (_, Some(b)) =>
         var z := b;
       case _ =>
     }
   }
   assert z == 3;
}

method ModifiesFresh(w: Wrapper)
{
  opaque modifies {} 
  {
    var wrapper := new Wrapper;
    wrapper.x := 2;
    w.x := 3;
  }
}

method ImplicitModifiesClause(w: Wrapper)
  modifies w
{
  w.x := 2;
  opaque
  {
    w.x := 3;
  }
  assert w.x == 2;
}

method FreshEnsures() {
  var c: object;
  opaque
    ensures fresh(c) // !old(allocated(c)) && allocated(c)
  {
    c := new object;
  }
  assert false;
}

class GranularModifies
{
  var x : int
  var y : int
  var objects: set<GranularModifies>

  method foo()
    modifies this
    ensures x == 1
    ensures y == 1
  {
    x := 1;
    objects := {this};
    opaque
      modifies objects`y
      ensures y == 1
      // ensures x == 1
    {
      y := 1;
    }
  }
}