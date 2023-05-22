// RUN: %dafny /compile:3 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Main()
{
  test0(10);
	test5(11);
	test6(12);
	test1();
	test2();
}

ghost predicate valid(x:int)
{
  x > 0
}

ghost function ref1(y:int) : int
  requires valid(y);
{
  y - 1
}

lemma assumption1()
  ensures forall a, b :: valid(a) && valid(b) && ref1(a) == ref1(b) ==> a == b;
{
}

method test0(a: int)
{
  if ref1.requires(a) {
    // the precondition should suffice to let us call the method
    ghost var b := ref1(a);
  }
}
method test5(a: int)
{
  if valid(a) {
    // valid(a) is the precondition of ref1
    assert ref1.requires(a);
  }
}
method test6(a: int)
{
  if ref1.requires(a) {
    // the precondition of ref1 is valid(a)
    assert valid(a);
  }
}

method test1()
{
  if * {
    assert forall a, b :: valid(a) && valid(b) && ref1(a) == ref1(b) ==> a == b;
  } else {
    assert forall a, b :: ref1.requires(a) && ref1.requires(b) && ref1(a) == ref1(b)
                          ==> a == b;
  }
}

ghost function {:opaque} ref2(y:int) : int        // Now with an opaque attribute
  requires valid(y);
{
  y - 1
}

lemma assumption2()
  ensures forall a, b :: valid(a) && valid(b) && ref2(a) == ref2(b) ==> a == b;
{
  reveal ref2();
}

method test2()
{
  assumption2();
  if * {
    assert forall a, b :: valid(a) && valid(b) && ref2(a) == ref2(b) ==> a == b;
  } else {
    assert forall a, b :: ref2.requires(a) && ref2.requires(b) && ref2(a) == ref2(b)
                          ==> a == b;
  }
}
