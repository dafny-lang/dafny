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

function {:extern} Bar(x: int, ghost z: int): (y: int)
  requires 1 < x < 10
  requires z > x
  ensures y >= 10
  ensures y > z

function BarCaller(x: int): (y: int)
  requires 1 < x < 10
  ensures y >= 10
{
  Bar(x, 20)
}

method {:test} BarTest()
{
  var y := Bar(3, 20);
  expect y == 30;
}

function {:extern} FunctionWithUnnamedResult(x: int): int 
  requires x > 3
  ensures x > 3

method {:test} FunctionWithUnnamedResultTest()
{
  var y1 := FunctionWithUnnamedResult(4);
  var y2 := FunctionWithUnnamedResult(3); // Fails
  expect false;
}

function {:extern} GenFunction<T>(x: int, y: T): T
  requires x > 3

method {:test} GenFunctionTest()
{
  var y1 := GenFunction(4, 10);
  var y2 := GenFunction(3, 10); // Fails
  expect false;
}

method {:extern} GenMethod<T>(x: int, y: T) returns (z: T)
  requires x > 3

method {:test} GenMethodTest()
{
  var y1 := GenMethod(4, 10);
  var y2 := GenMethod(3, 10); // Fails
  expect false;
}

function {:extern} Baz(x: int): (y: int)
  ensures y == x

method {:test} BazTest()
{
  var y := Baz(3);
  // An extra check just for fun. The auto-generated wrapper should
  // already ensure that y == 3.
  expect y != 7;
}
