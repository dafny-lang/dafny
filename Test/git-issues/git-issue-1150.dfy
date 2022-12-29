// RUN: %baredafny run %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Foo = Foo(x: nat)
{
  // the following once generated malformed Boogie
  const good?: bool := 0 < x < 5;
}

method Main()
{
  var x := Foo(2);
  assert x.good?;
  print x, " ", x.good?, "\n";

  var y := Foo(5);
  assert !y.good?;
  print y, " ", y.good?, "\n";
}
