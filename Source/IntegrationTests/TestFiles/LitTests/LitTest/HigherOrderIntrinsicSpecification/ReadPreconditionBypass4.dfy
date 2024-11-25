// RUN: %exits-with 4 %verify "%s" > "%t"
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

method M()
  ensures false
{
  var outer := new Ref();

  var myg := myf.requires;
  var myh := myg.requires;

  var inner1 := new Ref();
  outer.inner := inner1;
  var reads1 := myh.reads(outer);
  assert reads1 == {inner1}; // Error: assertion might not hold
}

method M2()
  ensures false
{
  var outer := new Ref();

  var myg := myf.requires;
  var myh := myg.requires;

  var inner2 := new Ref();
  outer.inner := inner2;
  var reads2 := myh.reads(outer);
  assert reads2 == {inner2}; // Error: assertion might not hold
}
