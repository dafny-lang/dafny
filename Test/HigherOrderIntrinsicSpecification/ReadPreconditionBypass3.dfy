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

  var myg := myf.requires;

  var inner1 := new Ref();
  outer.inner := inner1;
  var reads1 := myg.reads(outer);
  assert reads1 == {inner1}; // Error: assertion might not hold

  var inner2 := new Ref();
  outer.inner := inner2;
  var reads2 := myg.reads(outer);
  assert reads2 == {inner2}; // Error: assertion might not hold
}