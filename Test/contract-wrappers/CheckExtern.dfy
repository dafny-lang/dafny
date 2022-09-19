method {:extern} Foo(x: int) returns (y: int)
  requires 1 < x < 10
  ensures y >= 10

method FooCaller(x: int) returns (y: int)
  requires 1 < x < 10
  ensures y >= 10
{
  y := Foo(x);
}

method {:test} FooTest()
{
  var y := Foo(3);
  expect y == 30;
}

function method {:extern} Bar(x: int, ghost z: int): (y: int)
  requires 1 < x < 10
  requires z > x
  ensures y >= 10
  ensures y > z

function method BarCaller(x: int): (y: int)
  requires 1 < x < 10;
  ensures y >= 10;
{
  Bar(x, 20)
}

method {:test} BarTest()
{
  var y := Bar(3, 20);
  expect y == 30;
}
