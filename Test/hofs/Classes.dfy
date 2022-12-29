// RUN: %exits-with 4 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"


class C {
  static function method Static() : bool
  {
    true
  }
}

method K() {
  var f := C.Static;
  var o : object?;
  assert o !in f.reads();
  assert f.requires();
  assert f();
}


class T {
  var h : int ~> int
}

function B(t : T) : int ~> int
  reads t
{
  t.h
}

function J(t : T) : int
  reads t
  reads t.h.reads(0)
{
  if t.h.requires(0) then
    B(t)(0)
  else
    B(t)(0)  // error: precondition violation
}

method U(t : T)
  modifies t
{
  t.h := x => x;
  assert J(t) == 0; // ok
}

class MyClass {
  var data: int
	function method F(): int
	  reads this
	{
	  data
	}
  method M(that: MyClass)
	{
	  var fn := that.F;  // "that" is captured into the closure
	  var d := fn();
		assert d == that.data;  // yes
		assert d == this.data;  // error: no reason to believe that this would hold
	}
}
