// RUN: %dafny_0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type MyType  // compile error: opaque type
iterator Iter()  // compile error: body-less iterator
ghost method M()  // compile error: body-less ghost method
method P()  // compile error: body-less method
class TestClass {
  method Q()
  {
    if g == 0 {
      assume true;  // compile error: assume
    }
  }
  ghost var g: int;
}

function F(): int  // compile error: body-less ghost function
function method H(): int  // compile error: body-less function method

lemma Lemma() {
  assume false;  // compile error: assume
}
ghost method GMethod() {
  assume false;  // compile error: assume
}

function MyFunction(): int
{
  assume false;  // compile error: assume
  6
}

function MyCalcFunction(): int
{
  calc <= {
    2;
    6;
    { assume true; }  // compile error: assume
    10;
  }
  12
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
