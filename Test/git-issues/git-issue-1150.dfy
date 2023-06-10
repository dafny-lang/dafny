// RUN: %testDafnyForEachCompiler "%s" -- --relax-definite-assignment

datatype Foo = Foo(x: nat)
{
  // the following once generated malformed Boogie
  const good?: bool := 0 < x < 5
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
