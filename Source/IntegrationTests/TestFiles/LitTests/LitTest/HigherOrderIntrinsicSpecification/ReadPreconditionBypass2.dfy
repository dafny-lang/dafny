// RUN: %exits-with 4 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Ref {
  var inner: Ref
  constructor()
}

function myf(o: Ref): ()
  requires false
  reads o.inner
{
  ()
}

method Main()
  ensures false
{
  var outer := new Ref();

  var hof := myf.reads;

  var inner1 := new Ref();
  outer.inner := inner1;
  var reads1 := hof(outer); // Error: function precondition could not be proved
  assert reads1 == {inner1};

  var inner2 := new Ref();
  outer.inner := inner2;
  var reads2 := hof(outer);
  assert reads2 == {inner2};
}