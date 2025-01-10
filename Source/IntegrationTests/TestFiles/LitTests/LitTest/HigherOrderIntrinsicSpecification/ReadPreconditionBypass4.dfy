// RUN: %exits-with 4 %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Ref {
  var inner: Ref
  constructor() {
    inner := this;
  }
}

function myf(o: Ref): ()
  requires false
  reads o.inner
{
  ()
}

method M()
{
  var outer := new Ref();

  var myg := myf.requires;
  var myh := myg.requires;

  var inner1 := new Ref();
  outer.inner := inner1;
  var reads1 := myg.reads(outer);
  var reads2 := myh.reads(outer);
  assert reads1 == reads2;
  assert reads2 == {inner1}; // Error: assertion might not hold
  assert false; // we don't know what the reads clause is, because the precondition of myf does not hold.
}

method M2()
{
  var outer := new Ref();

  var myg := myf.requires;
  var myh := myg.requires;

  var inner2 := new Ref();
  outer.inner := inner2;
  var reads2 := myh.reads(outer);
  assert reads2 == {inner2}; // Error: assertion might not hold
  assert false; // we don't know what the reads clause is, because the precondition of myf does not hold.
}
