// RUN: %baredafny run %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Main()
{
  TestReals();
}

// This method produces an auto-initialized value
method Init<T(0)>() returns (t: T)
{
}

method TestReals()
{
  // Several of the cases below are regression tests of things that hadn't
  // worked properly before.

  var r: real;
  var s := r + 3.4;
  print "r= ", r, "  s= ", s, "\n";

  var a: real := Init();
  var b := a + 3.4;
  var z := 0.0;
  print "a= ", a, "  b= ", b, "  z= ", z, "\n";
  print "a==z = ", a==z, "\n";

  a := 2.0 / 3.0;
  b := a - a;
  print "a= ", a, "  b= ", b, "  z= ", z, "\n";
  print "b==z = ", b==z, "\n";

  var x := z as int;
  a := Init();
  var y := if a == 0.0 then a as int else 16;
  print "x= ", x, "  y= ", y, "\n";
}
