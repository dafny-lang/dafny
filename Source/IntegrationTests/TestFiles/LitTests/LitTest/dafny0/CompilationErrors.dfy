// RUN: %exits-with 3 %build "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type MyType
iterator Iter() 
ghost method M() ensures false  // compile error: body-less ghost method
method P() ensures false  // compile error: body-less method
class TestClass {
  method Q()
  {
    if g == 0 {
      assume true;  // compile error: assume
      assume {:axiom} true;
    }
  }
  ghost var g: int
}

ghost function F(): int ensures false // compile error: body-less ghost function
function H(): int ensures false // compile error: body-less function method

lemma Lemma() {
  assume false;  // compile error: assume
  assume {:axiom} true;
}
ghost method GMethod() {
  assume false;  // compile error: assume
  assume {:axiom} true;
}

ghost function MyFunction(): int
{
  assume false;  // compile error: assume
  assume {:axiom} true;
  6
}

ghost function MyCalcFunction(): int
{
  calc <= {
    2;
    6;
    { assume true; // compile error: assume
      assume {:axiom} true; }
    10;
  }
  12
}

datatype Result = Failure {
  predicate IsFailure() { true }
  function Extract() : () requires false { () }
}
method MyResultMethod() returns (r: Result) {
  var x :- assume Failure(); // compile error: assume
  var y :- assume {:axiom} Failure();
}

method MyAssignSuchThat() {
  var x: int :| assume false; // compile error: assume
  var y: int :| assume {:axiom} true;
}

// -------------------------- body-less loops

method BodyLessLoop_NonGhost(y: int)
  requires y <= 100
  ensures false
{
  var x := y;
  while true  // error: cannot be compiled
    invariant x <= 100
  for i := 0 to 100  // error: cannot be compiled
    invariant x <= 100
}

method BodyLessLoop_Ghost(ghost y: int)
  requires y <= 100
  ensures false
{
  if y == y {  // that makes this a ghost statement
    var x := y;
    while true  // error: cannot be compiled
      invariant x <= 100
    for i := 0 to 100  // error: cannot be compiled
      invariant x <= 100
  }
}
